#!/usr/bin/env python3
"""
caMMa — clawbot companion (but better)

Single-file local app for:
- safe JSON-RPC inspection (no signing, no key custody)
- ABI encoding/decoding for common EVM types
- EIP-55 checksum tooling and selector derivation
- log/topic utilities + lightweight event decoding
- local "job payload" builder for VirtualMaximus90 + VM90_ClawRouter
- offline simulation helpers (queue windows, fee math, bounded fanout checks)

Design constraints:
- Standard library only (no external deps).
- Avoids private key handling entirely.
- Intended for operator workflows: build payloads, verify addresses, query chain state.
"""

from __future__ import annotations

import argparse
import base64
import binascii
import dataclasses
import datetime as _dt
import decimal
import hashlib
import hmac
import http.server
import io
import json
import os
import platform
import random
import re
import socketserver
import struct
import sys
import textwrap
import threading
import time
import traceback
import typing as t
import urllib.error
import urllib.parse
import urllib.request
import uuid


# =============================================================
# Errors / small utilities
# =============================================================


class CaMMaError(Exception):
    pass


def now_utc() -> _dt.datetime:
    return _dt.datetime.now(tz=_dt.timezone.utc)


def iso_utc(ts: t.Optional[float] = None) -> str:
    d = now_utc() if ts is None else _dt.datetime.fromtimestamp(ts, tz=_dt.timezone.utc)
    return d.isoformat().replace("+00:00", "Z")


def clamp_int(v: int, lo: int, hi: int) -> int:
    if v < lo:
        return lo
    if v > hi:
        return hi
    return v


def json_dumps(obj: t.Any, pretty: bool = False) -> str:
    if pretty:
        return json.dumps(obj, indent=2, sort_keys=True, ensure_ascii=False)
    return json.dumps(obj, separators=(",", ":"), ensure_ascii=False)


def is_hex(s: str) -> bool:
    return bool(re.fullmatch(r"0x[0-9a-fA-F]*", s or ""))


def strip_0x(s: str) -> str:
    s = (s or "").strip()
    return s[2:] if s.lower().startswith("0x") else s


def add_0x(s: str) -> str:
    s = (s or "").strip()
    if s.lower().startswith("0x"):
        return "0x" + s[2:]
    return "0x" + s


def to_int_auto(s: str) -> int:
    s = s.strip()
    if s.lower().startswith("0x"):
        return int(s, 16)
    return int(s, 10)


def to_hex_int(n: int) -> str:
    if n < 0:
        raise CaMMaError("negative integers cannot be encoded to hex")
    return hex(n)


def human_bytes(n: int) -> str:
    units = ["B", "KB", "MB", "GB", "TB", "PB"]
    x = float(n)
    i = 0
    while x >= 1024.0 and i < len(units) - 1:
        x /= 1024.0
        i += 1
    if i == 0:
        return f"{int(x)} {units[i]}"
    return f"{x:.2f} {units[i]}"


def short_id(prefix: str = "cam") -> str:
    return f"{prefix}-{uuid.uuid4().hex[:14]}"


def wrap(s: str, width: int = 92) -> str:
    return "\n".join(textwrap.wrap(s, width=width, replace_whitespace=False))


def jitter_ms(ms: int, spread: int = 55) -> None:
    r = random.randint(-spread, spread)
    time.sleep(max(0.0, (ms + r) / 1000.0))


# =============================================================
# Pure Python Keccak-256 (Ethereum) implementation
# - This is a compact, self-contained variant intended for tooling.
# - It supports only the fixed-rate keccak256 use case.
# =============================================================


_KECCAK_R = 1088
_KECCAK_C = 512
_KECCAK_RATE_BYTES = _KECCAK_R // 8
_KECCAK_ROUNDS = 24

_KECCAK_RC = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808A,
    0x8000000080008000,
    0x000000000000808B,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008A,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000A,
    0x000000008000808B,
    0x800000000000008B,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800A,
    0x800000008000000A,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
]

_KECCAK_RHO = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
]


def _rotl64(x: int, n: int) -> int:
    n &= 63
    return ((x << n) | (x >> (64 - n))) & 0xFFFFFFFFFFFFFFFF


