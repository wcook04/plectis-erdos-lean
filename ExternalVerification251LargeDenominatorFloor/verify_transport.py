#!/usr/bin/env python3
"""Check pinned target bytes and replay integer arithmetic, without compiling Lean.

This is preparatory evidence, never a Lean, Comparator or independent-kernel receipt.
"""
from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path
import re
import sys


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def check_module_identity(root: Path, rows: list[dict]) -> None:
    for row in rows:
        raw = (root / row["target_path"]).read_bytes()
        port = row.get("target_toolchain_port")
        if port is not None:
            require(isinstance(port, dict) and
                    re.fullmatch(r"[0-9a-f]{40}", port.get("commit", "")) is not None and
                    re.fullmatch(r"[0-9a-f]{64}", port.get("sha256", "")) is not None and
                    bool(port.get("reason")),
                    "Incomplete target toolchain port: " + row["target_path"])
        expected = port["sha256"] if port is not None else row["sha256"]
        require(hashlib.sha256(raw).hexdigest() == expected,
                "Pinned target drift: " + row["target_path"])

def main() -> None:
    sys.set_int_max_str_digits(0)
    family = Path(__file__).resolve().parent
    root = family.parent
    manifest = json.loads((family / "source-transport.json").read_text())
    check_module_identity(root, manifest["modules"])
    for name, row in manifest["target_environment"].items():
        require(hashlib.sha256((root / name).read_bytes()).hexdigest() == row["sha256"],
                "Target environment drift: " + name)
    source = root / "ErdosProblems/Erdos251"
    text = (source / "PaperLargeStreamingV5.lean").read_text()
    constants = {}
    for name in ("c", "X", "u", "v", "up", "vp"):
        match = re.search(r"^def " + name + r" : ℕ := (\d+)\s*$", text, re.M)
        require(match is not None, "Missing exact natural constant: " + name)
        constants[name] = int(match.group(1))
    c, X = constants["c"], constants["X"]
    sieve = bytearray(b"\1") * X
    sieve[:2] = b"\0\0"
    for p in range(2, math.isqrt(X - 1) + 1):
        if sieve[p]:
            start = p * p
            sieve[start:X:p] = b"\0" * ((X - 1 - start) // p + 1)
    count, prefix = 0, 0
    for p in range(2, X):
        if sieve[p]:
            count += 1
            prefix = 2 * prefix + p
    chunk = (source / "StreamingChunksV5/Chunk0250.lean").read_text()
    state = re.search(r"^def state0250 : ℕ × ℕ := \((\d+), (\d+)\)", chunk, re.M)
    require(state is not None, "Missing final certificate state")
    require((count, prefix) == (int(state.group(1)), int(state.group(2))),
            "Independent prime-prefix replay disagrees with the final chunk")
    u, v, up, vp = (constants[name] for name in ("u", "v", "up", "vp"))
    checks = {
        "prime_count": count == c,
        "positive_denominators": v > 0 and vp > 0,
        "farey_determinant_one": up * v - u * vp == 1,
        "strict_lower_bracket": u * 2**c < prefix * v,
        "strict_upper_bracket": (2 * prefix + 5000 * (c + 1)**4) * vp < up * 2**(c + 1),
        "strong_binary_floor": 2**40062 <= v + vp,
        "strong_decimal_floor": 10**12059 < 2**40062,
        "printed_binary_floor": 2**39997 <= 2**40062,
        "printed_decimal_floor": 10**12040 < 2**39997,
    }
    require(all(checks.values()), "Arithmetic failure: " + str(checks))
    print(json.dumps({
        "evidence_class": "source_bytes_and_independent_integer_replay_only",
        "lean_comparator_and_independent_kernel": "pending",
        "source_commit": manifest["source_commit"],
        "source_modules": len(manifest["modules"]),
        "prime_count": count,
        "prime_cutoff": X,
        "denominator_sum_bits": (v + vp).bit_length(),
        "checks": checks,
    }, indent=2))


if __name__ == "__main__":
    main()
