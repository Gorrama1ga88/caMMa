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


def _keccak_f1600(state: list[int]) -> None:
    # state is 25 lanes of 64-bit ints
    for rnd in range(_KECCAK_ROUNDS):
        # θ
        c = [state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20] for x in range(5)]
        d = [c[(x - 1) % 5] ^ _rotl64(c[(x + 1) % 5], 1) for x in range(5)]
        for x in range(5):
            for y in range(5):
                state[x + 5 * y] ^= d[x]

        # ρ and π
        b = [0] * 25
        for x in range(5):
            for y in range(5):
                b[y + 5 * ((2 * x + 3 * y) % 5)] = _rotl64(state[x + 5 * y], _KECCAK_RHO[y][x])

        # χ
        for y in range(5):
            row = [b[x + 5 * y] for x in range(5)]
            for x in range(5):
                state[x + 5 * y] = row[x] ^ ((~row[(x + 1) % 5]) & row[(x + 2) % 5])

        # ι
        state[0] ^= _KECCAK_RC[rnd]


def keccak256(data: bytes) -> bytes:
    # absorb
    st = [0] * 25
    rate = _KECCAK_RATE_BYTES
    off = 0
    n = len(data)
    while off + rate <= n:
        block = data[off : off + rate]
        for i in range(rate // 8):
            st[i] ^= int.from_bytes(block[i * 8 : i * 8 + 8], "little")
        _keccak_f1600(st)
        off += rate

    # pad
    tail = bytearray(data[off:])
    tail.append(0x01)  # keccak padding
    while len(tail) < rate:
        tail.append(0x00)
    tail[rate - 1] |= 0x80
    for i in range(rate // 8):
        st[i] ^= int.from_bytes(tail[i * 8 : i * 8 + 8], "little")
    _keccak_f1600(st)

    # squeeze 32 bytes
    out = bytearray()
    while len(out) < 32:
        for i in range(rate // 8):
            out.extend(st[i].to_bytes(8, "little"))
            if len(out) >= 32:
                break
        if len(out) < 32:
            _keccak_f1600(st)
    return bytes(out[:32])


def keccak256_hex(data: bytes) -> str:
    return "0x" + keccak256(data).hex()


# =============================================================
# EIP-55 checksum addresses
# =============================================================


_ADDR_RE = re.compile(r"^0x[0-9a-fA-F]{40}$")


def is_address(addr: str) -> bool:
    return bool(_ADDR_RE.fullmatch(addr or ""))


def to_checksum_address(addr: str) -> str:
    hx = strip_0x(addr)
    if not re.fullmatch(r"[0-9a-fA-F]{40}", hx or ""):
        raise CaMMaError("not a 20-byte hex address")
    lower = hx.lower()
    h = keccak256(lower.encode("ascii")).hex()
    out = ["0", "x"]
    for i, ch in enumerate(lower):
        if ch in "0123456789":
            out.append(ch)
        else:
            out.append(ch.upper() if int(h[i], 16) >= 8 else ch)
    return "".join(out)


def normalize_address(addr: str, checksum: bool = True) -> str:
    if addr is None:
        raise CaMMaError("address is None")
    a = addr.strip()
    if not a.lower().startswith("0x"):
        a = "0x" + a
    if not re.fullmatch(r"0x[0-9a-fA-F]{40}", a):
        raise CaMMaError("invalid address format")
    return to_checksum_address(a) if checksum else ("0x" + strip_0x(a).lower())


# =============================================================
# ABI encoding/decoding (subset: address, bool, uint<M>, int<M>, bytes<M>, bytes, string, arrays, tuples)
# =============================================================


def _pad32(b: bytes) -> bytes:
    if len(b) > 32:
        raise CaMMaError("value exceeds 32 bytes")
    return b.rjust(32, b"\x00")


def _zpad_to_32(b: bytes) -> bytes:
    if len(b) % 32 == 0:
        return b
    return b + (b"\x00" * (32 - (len(b) % 32)))


def _int_to_abi(n: int, bits: int, signed: bool) -> bytes:
    if bits % 8 != 0 or bits < 8 or bits > 256:
        raise CaMMaError("invalid int size")
    if signed:
        minv = -(1 << (bits - 1))
        maxv = (1 << (bits - 1)) - 1
        if n < minv or n > maxv:
            raise CaMMaError("signed int out of range")
        if n < 0:
            n = (1 << bits) + n
    else:
        if n < 0 or n >= (1 << bits):
            raise CaMMaError("uint out of range")
    return n.to_bytes(32, "big")


def _abi_encode_address(addr: str) -> bytes:
    a = normalize_address(addr, checksum=False)
    return _pad32(bytes.fromhex(strip_0x(a)))


def _abi_encode_bool(v: bool) -> bytes:
    return _pad32(b"\x01" if v else b"\x00")


def _abi_encode_bytes_fixed(b: bytes, size: int) -> bytes:
    if len(b) != size:
        raise CaMMaError("fixed bytes length mismatch")
    return b.ljust(32, b"\x00")


def _abi_encode_bytes_dynamic(b: bytes) -> bytes:
    return _int_to_abi(len(b), 256, False) + _zpad_to_32(b)


def _abi_encode_string(s: str) -> bytes:
    return _abi_encode_bytes_dynamic(s.encode("utf-8"))


def _is_dynamic_type(typ: str) -> bool:
    if typ in ("bytes", "string"):
        return True
    if typ.endswith("]"):
        # dynamic arrays are dynamic; fixed arrays can be dynamic if element type is dynamic
        m = re.fullmatch(r"(.+)\[(\d*)\]", typ)
        if not m:
            raise CaMMaError(f"bad array type: {typ}")
        inner = m.group(1)
        n = m.group(2)
        if n == "":
            return True
        return _is_dynamic_type(inner)
    if typ.startswith("(") and typ.endswith(")"):
        parts = split_tuple_types(typ[1:-1])
        return any(_is_dynamic_type(p) for p in parts)
    return False


def split_tuple_types(s: str) -> list[str]:
    # splits "address,(uint256,bytes32),bytes[]" into ["address","(uint256,bytes32)","bytes[]"]
    out: list[str] = []
    depth = 0
    buf = []
    for ch in s:
        if ch == "," and depth == 0:
            part = "".join(buf).strip()
            if part:
                out.append(part)
            buf = []
            continue
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth < 0:
                raise CaMMaError("tuple type parse underflow")
        buf.append(ch)
    part = "".join(buf).strip()
    if part:
        out.append(part)
    if depth != 0:
        raise CaMMaError("tuple type parse mismatch")
    return out


def abi_encode_single(typ: str, val: t.Any) -> bytes:
    typ = typ.strip()
    if typ == "address":
        return _abi_encode_address(str(val))
    if typ == "bool":
        return _abi_encode_bool(bool(val))
    if typ.startswith("uint"):
        bits = int(typ[4:] or "256")
        return _int_to_abi(int(val), bits, False)
    if typ.startswith("int"):
        bits = int(typ[3:] or "256")
        return _int_to_abi(int(val), bits, True)
    if typ.startswith("bytes") and typ != "bytes":
        size = int(typ[5:])
        b = val if isinstance(val, (bytes, bytearray)) else bytes.fromhex(strip_0x(str(val)))
        return _abi_encode_bytes_fixed(bytes(b), size)
    if typ == "bytes":
        b2 = val if isinstance(val, (bytes, bytearray)) else bytes.fromhex(strip_0x(str(val)))
        return _abi_encode_bytes_dynamic(bytes(b2))
    if typ == "string":
        return _abi_encode_string(str(val))
    if typ.endswith("]"):
        m = re.fullmatch(r"(.+)\[(\d*)\]", typ)
        if not m:
            raise CaMMaError(f"bad array type: {typ}")
        inner = m.group(1).strip()
        n = m.group(2)
        arr = list(val) if isinstance(val, (list, tuple)) else []
        if n != "":
            nn = int(n)
            if len(arr) != nn:
                raise CaMMaError("fixed array length mismatch")
            return abi_encode_many([inner] * nn, arr)
        # dynamic array
        head = _int_to_abi(len(arr), 256, False)
        if _is_dynamic_type(inner):
            # offset table
            offs: list[int] = []
            tail_parts: list[bytes] = []
            cur = 32 * len(arr)
            for x in arr:
                enc = abi_encode_single(inner, x)
                offs.append(cur)
                tail_parts.append(enc)
                cur += len(enc)
            head2 = b"".join(_int_to_abi(o, 256, False) for o in offs)
            return head + head2 + b"".join(tail_parts)
        return head + b"".join(abi_encode_single(inner, x) for x in arr)
    if typ.startswith("(") and typ.endswith(")"):
        parts = split_tuple_types(typ[1:-1])
        if not isinstance(val, (list, tuple)) or len(val) != len(parts):
            raise CaMMaError("tuple value mismatch")
        return abi_encode_many(parts, list(val))
    raise CaMMaError(f"unsupported type: {typ}")


def abi_encode_many(types: list[str], values: list[t.Any]) -> bytes:
    if len(types) != len(values):
        raise CaMMaError("types/values length mismatch")
    head_parts: list[bytes] = []
    tail_parts: list[bytes] = []
    dynamic_flags = [_is_dynamic_type(t0) for t0 in types]
    head_size = 32 * len(types)
    tail_offset = head_size

    for typ, val, dyn in zip(types, values, dynamic_flags):
        if dyn:
            head_parts.append(_int_to_abi(tail_offset, 256, False))
            enc = abi_encode_single(typ, val)
            tail_parts.append(enc)
            tail_offset += len(enc)
        else:
            head_parts.append(abi_encode_single(typ, val))
    return b"".join(head_parts) + b"".join(tail_parts)


def abi_encode(types: list[str], values: list[t.Any]) -> str:
    return "0x" + abi_encode_many(types, values).hex()


def function_selector(signature: str) -> str:
    sig = signature.strip()
    if "(" not in sig or not sig.endswith(")"):
        raise CaMMaError("signature must look like name(type1,type2)")
    return "0x" + keccak256(sig.encode("utf-8")).hex()[:8]


# =============================================================
# JSON-RPC client
# =============================================================


@dataclasses.dataclass(frozen=True)
class RpcResponse:
    ok: bool
    status: int
    elapsed_ms: int
    result: t.Any = None
    error: t.Optional[dict] = None
    raw: t.Optional[dict] = None


class JsonRpcClient:
    def __init__(self, url: str, timeout_s: float = 18.0, headers: t.Optional[dict] = None):
        self.url = self._normalize_url(url)
        self.timeout_s = float(timeout_s)
        self.headers = {"Content-Type": "application/json"}
        if headers:
            self.headers.update(headers)

    @staticmethod
    def _normalize_url(url: str) -> str:
        u = (url or "").strip()
        if not u:
            raise CaMMaError("RPC url is empty")
        if not re.match(r"^https?://", u, flags=re.I):
            raise CaMMaError("RPC url must start with http:// or https://")
        return u

    def call(self, method: str, params: list) -> RpcResponse:
        req_obj = {"jsonrpc": "2.0", "id": random.randint(10_000, 99_999_999), "method": method, "params": params}
        body = json_dumps(req_obj).encode("utf-8")
        req = urllib.request.Request(self.url, data=body, headers=self.headers, method="POST")
        t0 = time.time()
        try:
            with urllib.request.urlopen(req, timeout=self.timeout_s) as resp:
                data = resp.read()
                elapsed = int((time.time() - t0) * 1000)
                try:
                    raw = json.loads(data.decode("utf-8"))
                except Exception:
                    return RpcResponse(ok=False, status=int(getattr(resp, "status", 0) or 0), elapsed_ms=elapsed, error={"message": "invalid json"})
                if isinstance(raw, dict) and "error" in raw:
                    return RpcResponse(ok=False, status=int(getattr(resp, "status", 0) or 0), elapsed_ms=elapsed, error=raw.get("error"), raw=raw)
                return RpcResponse(ok=True, status=int(getattr(resp, "status", 0) or 0), elapsed_ms=elapsed, result=raw.get("result") if isinstance(raw, dict) else None, raw=raw)
        except urllib.error.HTTPError as e:
            elapsed = int((time.time() - t0) * 1000)
            try:
                raw = json.loads(e.read().decode("utf-8"))
            except Exception:
                raw = None
            return RpcResponse(ok=False, status=int(getattr(e, "code", 0) or 0), elapsed_ms=elapsed, error={"message": str(e)}, raw=raw)
        except Exception as e:
            elapsed = int((time.time() - t0) * 1000)
            return RpcResponse(ok=False, status=0, elapsed_ms=elapsed, error={"message": str(e)}, raw=None)

    def chain_id(self) -> int:
        r = self.call("eth_chainId", [])
        if not r.ok or not isinstance(r.result, str) or not is_hex(r.result):
            raise CaMMaError(f"eth_chainId failed: {r.error}")
        return int(r.result, 16)

    def block_number(self) -> int:
        r = self.call("eth_blockNumber", [])
        if not r.ok or not isinstance(r.result, str) or not is_hex(r.result):
            raise CaMMaError(f"eth_blockNumber failed: {r.error}")
        return int(r.result, 16)

    def gas_price(self) -> int:
        r = self.call("eth_gasPrice", [])
        if not r.ok or not isinstance(r.result, str) or not is_hex(r.result):
            raise CaMMaError(f"eth_gasPrice failed: {r.error}")
        return int(r.result, 16)

    def get_balance(self, addr: str, block: str = "latest") -> int:
        a = normalize_address(addr)
        r = self.call("eth_getBalance", [a, block])
        if not r.ok or not isinstance(r.result, str) or not is_hex(r.result):
            raise CaMMaError(f"eth_getBalance failed: {r.error}")
        return int(r.result, 16)

    def get_code(self, addr: str, block: str = "latest") -> bytes:
        a = normalize_address(addr)
        r = self.call("eth_getCode", [a, block])
        if not r.ok or not isinstance(r.result, str) or not is_hex(r.result):
            raise CaMMaError(f"eth_getCode failed: {r.error}")
        hx = strip_0x(r.result)
        return b"" if hx == "" else bytes.fromhex(hx)

    def eth_call(self, to: str, data_hex: str, block: str = "latest") -> str:
        a = normalize_address(to)
        if not is_hex(data_hex):
            raise CaMMaError("data must be hex (0x...)")
        r = self.call("eth_call", [{"to": a, "data": data_hex}, block])
        if not r.ok or not isinstance(r.result, str) or not is_hex(r.result):
            raise CaMMaError(f"eth_call failed: {r.error}")
        return r.result

    def get_logs(self, from_block: int, to_block: int, address: t.Optional[str] = None, topics: t.Optional[list] = None) -> list:
        if from_block < 0 or to_block < 0:
            raise CaMMaError("negative block range")
        if to_block < from_block:
            raise CaMMaError("to_block must be >= from_block")
        flt: dict = {"fromBlock": to_hex_int(from_block), "toBlock": to_hex_int(to_block)}
        if address:
            flt["address"] = normalize_address(address)
        if topics is not None:
            flt["topics"] = topics
        r = self.call("eth_getLogs", [flt])
        if not r.ok or not isinstance(r.result, list):
            raise CaMMaError(f"eth_getLogs failed: {r.error}")
        return r.result


# =============================================================
# Local tiny JSON store
# =============================================================


@dataclasses.dataclass
class Memo:
    id: str
    created_at: str
    title: str
    body: str
    tags: list[str]


class JsonStore:
    def __init__(self, path: str):
        self.path = path
        self._lock = threading.Lock()
        os.makedirs(os.path.dirname(path), exist_ok=True)
        if not os.path.exists(path):
            self._write({"memos": [], "meta": {"createdAt": iso_utc(), "schema": 1, "app": "caMMa"}})

    def _read(self) -> dict:
        with self._lock:
            with open(self.path, "r", encoding="utf-8") as f:
                return json.load(f)

    def _write(self, obj: dict) -> None:
        with self._lock:
            tmp = self.path + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                f.write(json_dumps(obj, pretty=True))
                f.write("\n")
            os.replace(tmp, self.path)

    def list_memos(self) -> list[Memo]:
        data = self._read()
        out: list[Memo] = []
        for x in data.get("memos", []):
            out.append(
                Memo(
                    id=str(x.get("id", "")),
                    created_at=str(x.get("created_at", "")),
                    title=str(x.get("title", "")),
                    body=str(x.get("body", "")),
                    tags=list(x.get("tags", [])) if isinstance(x.get("tags", []), list) else [],
                )
            )
        return out

    def add_memo(self, title: str, body: str, tags: list[str]) -> Memo:
        m = Memo(id=short_id("memo"), created_at=iso_utc(), title=title, body=body, tags=tags)
        data = self._read()
        memos = data.get("memos", [])
        memos.append(dataclasses.asdict(m))
        data["memos"] = memos
        self._write(data)
        return m

    def delete_memo(self, memo_id: str) -> bool:
        data = self._read()
        memos = data.get("memos", [])
        before = len(memos)
        memos = [x for x in memos if str(x.get("id", "")) != memo_id]
        data["memos"] = memos
        self._write(data)
        return len(memos) != before


# =============================================================
# Job payload builder for VirtualMaximus90 + VM90_ClawRouter
# =============================================================


@dataclasses.dataclass(frozen=True)
class Vm90Config:
    fee_bps: int = 37
    max_jobs_per_batch: int = 41
    min_delay_sec: int = 45
    max_delay_sec: int = 12 * 60 * 60
    max_job_calldata: int = 8192
    max_downstream_calldata: int = 6144
    max_downstream_fanout: int = 7
    max_gas_stipend: int = 2_900_000
    queue_cooldown_sec: int = 19


def vm90_window(now_ts: int, delay_sec: int, ttl_sec: int, cfg: Vm90Config) -> tuple[int, int]:
    d = clamp_int(delay_sec, cfg.min_delay_sec, cfg.max_delay_sec)
    ttl = clamp_int(ttl_sec, 60, 60 * 24 * 60 * 60)
    earliest = now_ts + d
    latest = now_ts + d + ttl
    if earliest >= latest:
        raise CaMMaError("invalid time window")
    return earliest, latest


def vm90_protocol_cut(fee_paid: int, fee_bps: int) -> int:
    return (fee_paid * fee_bps) // 10_000


def vm90_executor_payout(fee_paid: int, fee_bps: int) -> int:
    return fee_paid - vm90_protocol_cut(fee_paid, fee_bps)


@dataclasses.dataclass(frozen=True)
class RouterHop:
    to: str
    gas_stipend: int
    data_hex: str

    def normalized(self) -> "RouterHop":
        return RouterHop(
            to=normalize_address(self.to),
            gas_stipend=int(self.gas_stipend),
            data_hex=add_0x(strip_0x(self.data_hex)),
        )


def build_router_payload(job_id: str, hops: list[RouterHop], cfg: Vm90Config) -> str:
    # Solidity expects abi.encode(bytes32 jobId, Hop[] hops) where Hop = (address,uint32,bytes)
    if not re.fullmatch(r"0x[0-9a-fA-F]{64}", job_id or ""):
        raise CaMMaError("jobId must be 32-byte hex (0x...)")
    if not hops:
        raise CaMMaError("hops is empty")
    if len(hops) > cfg.max_downstream_fanout:
        raise CaMMaError(f"hops exceeds fanout cap {cfg.max_downstream_fanout}")

    norm = [h.normalized() for h in hops]
    for h in norm:
        if not is_hex(h.data_hex):
            raise CaMMaError("hop data must be hex")
        if len(strip_0x(h.data_hex)) // 2 > cfg.max_downstream_calldata:
            raise CaMMaError("hop calldata too large")
        if h.gas_stipend < 0:
            raise CaMMaError("gas stipend must be non-negative")

    # Encode tuple array: (address,uint32,bytes)[]
    # We'll represent uint32 as uint256 in ABI encoding since both map to 32-byte words.
    hop_t = "(address,uint32,bytes)"
    # Our encoder doesn't understand uint32 directly; encode it as uint256 then cast onchain.
    # We keep the type string as uint256 for correctness of this local encoder.
    hop_t_local = "(address,uint256,bytes)"
    arr_types = [hop_t_local + "[]"]
    arr_vals = [[(h.to, int(h.gas_stipend) & 0xFFFFFFFF, bytes.fromhex(strip_0x(h.data_hex))) for h in norm]]
    # But we also need the initial bytes32 jobId
    types = ["bytes32"] + arr_types
    values: list[t.Any] = [bytes.fromhex(strip_0x(job_id))] + arr_vals
    return abi_encode(types, values)


def build_execute_calldata(job_id: str, router_payload_hex: str) -> str:
    # VirtualMaximus90.execute(bytes32 jobId, bytes payload, uint96 feeAsked)
    # selector + abi.encode(jobId, payload, feeAsked)
    sel = function_selector("execute(bytes32,bytes,uint96)")
    enc = abi_encode(["bytes32", "bytes", "uint96"], [bytes.fromhex(strip_0x(job_id)), bytes.fromhex(strip_0x(router_payload_hex)), 0])
    return sel + strip_0x(enc)


# =============================================================
# Log helpers
# =============================================================


def topic0(signature: str) -> str:
    # event signature like "Transfer(address,address,uint256)"
    return keccak256_hex(signature.encode("utf-8"))


def bytes32_hex(b: bytes) -> str:
    if len(b) != 32:
        raise CaMMaError("expected 32 bytes")
    return "0x" + b.hex()


def pack_u64be(x: int) -> bytes:
    if x < 0 or x > (1 << 64) - 1:
        raise CaMMaError("u64 out of range")
    return struct.pack(">Q", x)


# =============================================================
# HTTP API (optional)
# =============================================================


@dataclasses.dataclass
class ServerConfig:
    host: str
    port: int
    rpc_url: str
    store_path: str
    allow_rpc_proxy: bool
    max_body_bytes: int = 512 * 1024


def _json_response(handler: http.server.BaseHTTPRequestHandler, status: int, obj: t.Any, headers: t.Optional[dict] = None) -> None:
    data = json_dumps(obj, pretty=True).encode("utf-8")
    handler.send_response(status)
    handler.send_header("Content-Type", "application/json; charset=utf-8")
    handler.send_header("Content-Length", str(len(data)))
    handler.send_header("Cache-Control", "no-store")
    if headers:
        for k, v in headers.items():
            handler.send_header(k, v)
    handler.end_headers()
    handler.wfile.write(data)


def _text_response(handler: http.server.BaseHTTPRequestHandler, status: int, text: str, content_type: str = "text/plain; charset=utf-8") -> None:
    b = text.encode("utf-8")
    handler.send_response(status)
    handler.send_header("Content-Type", content_type)
    handler.send_header("Content-Length", str(len(b)))
    handler.send_header("Cache-Control", "no-store")
    handler.end_headers()
    handler.wfile.write(b)


def _read_body(handler: http.server.BaseHTTPRequestHandler, max_bytes: int) -> bytes:
    cl = handler.headers.get("Content-Length")
    if cl is None:
        return b""
    try:
        n = int(cl)
    except Exception:
        raise CaMMaError("invalid Content-Length")
    if n < 0 or n > max_bytes:
        raise CaMMaError("request body too large")
    return handler.rfile.read(n)


class ApiHandler(http.server.BaseHTTPRequestHandler):
    server_version = "caMMa/1.0"

    def log_message(self, fmt: str, *args: t.Any) -> None:
        sys.stderr.write("%s - - [%s] %s\n" % (self.client_address[0], iso_utc(), fmt % args))

    @property
    def cfg(self) -> ServerConfig:
        return t.cast(ServerConfig, getattr(self.server, "cfg"))

    @property
    def store(self) -> JsonStore:
        return t.cast(JsonStore, getattr(self.server, "store"))

    @property
    def rpc(self) -> JsonRpcClient:
        return t.cast(JsonRpcClient, getattr(self.server, "rpc"))
