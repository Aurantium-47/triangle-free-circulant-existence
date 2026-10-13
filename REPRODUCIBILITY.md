# Reproducing the formalization and finite checks

## Fixed Lean source and recorded run

The full theorem is `W16.exists_agraph` in
[lean-candidate/W16/Existence.lean](lean-candidate/W16/Existence.lean).
The recorded successful build is
[run 38442507918](https://github.com/Aurantium-47/triangle-free-circulant-existence/actions/runs/38442507918),
attempt 1, job 115452413854, at source commit
`01c614aa6e29c0fc88175fca249b17b5cfe65d1d`
(source tree `9aa33777ca0efea32ce8ddb037c5d7dca5387080`).
The documentation update does not change that tested source or claim a new run.

The environment is fixed by:

- [lean-toolchain](lean-candidate/lean-toolchain): `leanprover/lean4:v4.19.0`
  (reported Lean commit `6caaee842e94`).
- [lakefile.toml](lean-candidate/lakefile.toml): mathlib revision
  `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- [lake-manifest.json](lean-candidate/lake-manifest.json): nine exact package
  revisions, including mathlib. Use each resolved `rev`, rather than updating
  the manifest from a moving branch named in `inputRev`.

For the exact executed recipe, use the
[workflow at the tested commit](https://github.com/Aurantium-47/triangle-free-circulant-existence/blob/01c614aa6e29c0fc88175fca249b17b5cfe65d1d/.github/workflows/w16-circular-gaps-probe.yml).
It records the Ubuntu 24.04 runner setup, Lean distribution and binary checksums,
exact dependency checkouts, cache acquisition, ordered module compilation,
complete-type checks and transitive-axiom checks. A separate checkout of the
tested source can be obtained with:

```sh
git clone https://github.com/Aurantium-47/triangle-free-circulant-existence.git
cd triangle-free-circulant-existence
git checkout --detach 01c614aa6e29c0fc88175fca249b17b5cfe65d1d
```

The recipe compiles all 19 project modules into a new project output directory,
places that directory first in `LEAN_PATH`, excludes external copies of the
project modules, and checks that its audit imports use those fresh outputs.
It invokes Lean with `-j 1 -s 131072 -DElab.async=false`. It then prints the five
basic definitions and checks the complete types and transitive axiom dependencies
of the 61 declarations listed in the
[run summary](formalization/RUN_38442507918.json).

The preserved workflow is a historical, branch-scoped build recipe. Its old
title contains “not the full theorem”, and an old step label mentions only the
first lemma; the executed recipe at the linked commit actually checks the full
existence theorem. Its guards compare against the original release commit and
its trigger targets the existing candidate branch. It is not general-purpose
CI for a documentation-updated checkout or for `main`. To replay the historical
guards, use the exact tested source commit above. The workflow bytes are unchanged.

External mathlib and other dependency `.olean` caches are trusted inputs.
This run rebuilt the project modules, not all dependency sources; it did not
perform full dependency replay or an independent-kernel check. The final theorem's
reported axioms are `propext`, `Classical.choice`, and `Quot.sound`. Each of the
61 separately checked declarations uses only a subset of those three, with no
`sorryAx`, native-evaluation axiom or custom axiom in its reported dependency list.

The [complete expanded main type](formalization/MAIN_THEOREM_TYPE.txt) preserves
the actual output without elision. [FORMALIZATION.md](FORMALIZATION.md) explains
its mathematical meaning. This documentation preparation did not rerun Lean,
the finite verifier or the PDF compiler.

## Finite checks

`verify.py` checks the two circulant graph constructions associated with
Conjecture 3.8 in S. Masih Ayat, S. Majid Ayat, and Meysam Ghahramani,
*The independence number of circulant triangle-free graphs*,
AIMS Mathematics **5**(4) (2020), 3741–3750,
[doi:10.3934/math.2020242](https://doi.org/10.3934/math.2020242).
The proof describes a graph of order `n`, degree `2k+1`, and independence
number `2k+1` for every integer `k>=1` and even `6k+2<=n<=8k`.

The verifier uses only the Python standard library and requires Python 3.10
or later. The included results were generated with Python 3.12.10.
From this directory, run:

```sh
python verify.py > verification_stdout.txt
```

This writes `verification_results.json` and captures the per-case output in
`verification_stdout.txt`. The default run covers all 21 admissible pairs
with `1<=k<=6`, including both congruence classes of even `n`, both endpoints,
and the smallest case `(k,n)=(1,8)`. The largest tested graph has 48 vertices.
The JSON records the interpreter version, algorithm, parameters, connection
sets, mathematical results, and SHA-256 hash of the executed script.

For each pair, the program constructs the connection set directly from the
corresponding formula in the proof. It checks symmetry and exclusion of zero,
computes every vertex degree, examines every triple of vertices for a triangle,
and computes the exact independence number. The latter uses the recurrence

```text
alpha(G) = max(alpha(G - v), 1 + alpha(G - N[v])),
alpha(graph with no vertices) = 0,
```

with memoization. Both branches are evaluated; the computation does not assume
the claimed upper bound or require an independent set to contain a fixed vertex.
The expected value `2k+1` is compared with the computed result only afterward.
A failed check raises an exception. Validation is not disabled by Python's
optimization flag.

The included run passes all 21 cases: each graph has degree and independence
number `2k+1` and no triangles. These finite checks support reproducibility and
can detect errors in tested instances. They do **not** prove the statement for
all parameters; that conclusion depends on the mathematical proof. The JSON
is a record of the exact computations, not a formal proof certificate.

A different finite range can be selected explicitly:

```sh
python verify.py --max-k 4 --output results_k4.json
```

The exact independence-number recurrence can require exponentially increasing
time and memory as the range grows. The script does not install dependencies,
access the network, or modify its own source.

This work was completed with AI assistance.
