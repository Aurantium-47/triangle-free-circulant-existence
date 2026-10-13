# Triangle-free circulants with odd degree equal to their independence number

This note proves the existence assertion in Conjecture 3.8 of
Ayat, Ayat and Ghahramani (2020):

> For every integer k >= 1 and every even n with 6k + 2 <= n <= 8k,
> there is a simple undirected triangle-free circulant on n vertices
> whose degree and independence number both equal 2k + 1.

The proof covers both residue classes of even n modulo 4 and both endpoints.
It uses circular gaps for n divisible by 4 and cyclic-interval expansion
in a Chinese remainder representation for n congruent to 2 modulo 4.
The first construction extends the cited upper-endpoint construction.
No claim of bibliographic priority is made.

## Reading

- [English proof (PDF)](main.pdf)
- [Standalone LaTeX source](main.tex)
- [Chinese summary](SUMMARY_ZH.md)
- [References and attribution](REFERENCES.md)
- [Reproduction instructions](REPRODUCIBILITY.md)
- [Lean formalization and its verification scope](FORMALIZATION.md)
- [Rights and licensing notice](RIGHTS_AND_LICENSE.md)

## Lean formalization

The full existence statement is formalized as `W16.exists_agraph` in
[Existence.lean](lean-candidate/W16/Existence.lean). With Lean 4.19.0 and the
pinned mathlib revision, [GitHub Actions run 38442507918](https://github.com/Aurantium-47/triangle-free-circulant-existence/actions/runs/38442507918)
successfully compiled all 19 project modules at source commit
[`01c614aa6e29c0fc88175fca249b17b5cfe65d1d`](https://github.com/Aurantium-47/triangle-free-circulant-existence/commit/01c614aa6e29c0fc88175fca249b17b5cfe65d1d).
The run checked complete types and transitive axiom dependencies for 61
declarations. Five further basic definitions were printed, rather than each
receiving a separate axiom check; their dependencies are covered by the final
theorem's transitive check. Its axioms are `propext`, `Classical.choice` and
`Quot.sound`. See [FORMALIZATION.md](FORMALIZATION.md) for the exact statement,
the recorded evidence and the trusted external dependency-cache boundary.

The PDF and LaTeX manuscript remain the original **v0.1.0** documents. Their
statement that the result had not been formalized describes that version's
status; this documentation update supplies the subsequent formalization record.
The manuscript, finite-check code and recorded finite results are unchanged.

## Reproduction

The finite verifier requires Python 3.10 or later and uses only its standard
library. The included results were generated with Python 3.12.10:

~~~sh
python verify.py > verification_stdout.txt
~~~

It checks all 21 admissible pairs with 1 <= k <= 6, including degree,
triangles and the exact independence number. The output is in
verification_results.json. Finite checks do not prove the unbounded theorem.

The manuscript is a single LaTeX file with an embedded bibliography. A TeX
installation providing geometry, fontenc, lmodern, amsmath, amssymb, amsthm,
microtype and hyperref can compile it with:

~~~sh
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
~~~

The supplied PDF has five pages. All fonts are embedded.

## Status and files

This work was prepared with AI assistance. The Lean formalization has the
recorded verification scope described above; external precompiled dependencies
remain trusted inputs. No independent-kernel check or complete dependency-source
rebuild is claimed. It has not yet been reviewed by a human expert or undergone
journal peer review. The literature comparison does not establish priority.

PUBLIC_FILES.txt is the explicit list of files intended for distribution.
SHA256SUMS.txt hashes every other file on that list; it excludes itself
because a checksum list cannot normally contain its own final checksum.
Only the listed files belong to this public bundle.
