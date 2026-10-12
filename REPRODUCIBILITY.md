# Reproducing the finite checks

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
