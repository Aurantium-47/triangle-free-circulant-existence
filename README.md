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
- [Rights and licensing notice](RIGHTS_AND_LICENSE.md)

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

This work was prepared with AI assistance. It has not yet been reviewed by
a human expert or formalized in a proof assistant. It has not undergone
journal peer review. The literature comparison does not establish priority.

PUBLIC_FILES.txt is the explicit list of files intended for distribution.
SHA256SUMS.txt hashes every other file on that list; it excludes itself
because a checksum list cannot normally contain its own final checksum.
Only the listed files belong to this public bundle.
