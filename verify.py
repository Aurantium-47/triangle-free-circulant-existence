"""Finite exact checks for the two circulant graph constructions.

Reference: S. Masih Ayat, S. Majid Ayat, and Meysam Ghahramani,
The independence number of circulant triangle-free graphs,
AIMS Mathematics 5(4) (2020), 3741-3750, Conjecture 3.8.
DOI: 10.3934/math.2020242.
Finite checks do not prove the statement for all parameters.
"""
import argparse
import hashlib
import itertools
import json
import platform
from functools import lru_cache
from pathlib import Path


def connection_set(k, n):
    m = n // 2
    if n % 4 == 0:
        r = (8 * k - n) // 4
        a = k - r
        L = {s % n for j in range(a) for s in (2 * j + 1, -2 * j - 1)}
        E = {(m + 2 * j) % n for j in range(-r, r + 1)}
        return L | E
    t = (n - 4 * k + 2) // 4
    T = {j % m for j in range(1 - t, t)}
    U = set(range(2 * t - 1, 2 * k + 1))
    return {s for s in range(1, n)
            if (s % 2 == 1 and s % m in T) or (s % 2 == 0 and s % m in U)}


def independence_number(adjacency):
    @lru_cache(None)
    def alpha(vertices):
        if vertices == 0:
            return 0
        bit = vertices & -vertices
        vertex = bit.bit_length() - 1
        remaining = vertices ^ bit
        return max(alpha(remaining), 1 + alpha(remaining & ~adjacency[vertex]))
    value = alpha((1 << len(adjacency)) - 1)
    alpha.cache_clear()
    return value


def check_case(k, n):
    S = connection_set(k, n)
    if 0 in S or S != {(-s) % n for s in S}:
        raise ValueError(f"Invalid connection set: k={k}, n={n}")
    adjacency = [sum(1 << ((v + s) % n) for s in S) for v in range(n)]
    degrees = sorted({row.bit_count() for row in adjacency})
    triangles = sum(bool(adjacency[u] & (1 << v))
                    and bool(adjacency[u] & (1 << w))
                    and bool(adjacency[v] & (1 << w))
                    for u, v, w in itertools.combinations(range(n), 3))
    alpha = independence_number(adjacency)
    if degrees != [2 * k + 1] or triangles != 0 or alpha != 2 * k + 1:
        raise ValueError(f"Verification failed: k={k}, n={n}")
    return {"k": k, "n": n, "connection_set": sorted(S),
            "degrees": degrees, "triangles": triangles, "independence_number": alpha}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-k", type=int, default=6)
    parser.add_argument("--output", default="verification_results.json")
    args = parser.parse_args()
    if args.max_k < 1:
        parser.error("--max-k must be positive")
    cases = []
    for k in range(1, args.max_k + 1):
        for n in range(6 * k + 2, 8 * k + 1, 2):
            case = check_case(k, n)
            cases.append(case)
            print(json.dumps(case), flush=True)
    result = {
        "python_version": platform.python_version(),
        "algorithm": "exact vertex-deletion recurrence with memoization; all vertex triples for triangles",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "max_k": args.max_k, "case_count": len(cases),
        "all_checks_passed": True, "cases": cases,
    }
    Path(args.output).write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"case_count": len(cases), "all_checks_passed": True}), flush=True)


if __name__ == "__main__":
    main()
