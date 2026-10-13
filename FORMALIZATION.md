# Lean formalization of the existence theorem

`W16.exists_agraph` formalizes the full parameter range of Conjecture 3.8 of
Ayat, Ayat and Ghahramani (2020): every `k >= 1` and every even `n` with
`6*k + 2 <= n <= 8*k` admit a triangle-free circulant on `n` vertices whose
regular degree and independence number both equal `2*k + 1`.

## Statement and interpretation

The readable declaration in [Existence.lean](lean-candidate/W16/Existence.lean) is:

```lean
theorem exists_agraph
    {n k : ℕ} (hk : 1 ≤ k) (he : Even n)
    (hlo : 6 * k + 2 ≤ n) (hhi : n ≤ 8 * k) :
    letI : NeZero n := ⟨w16Parameters_ne_zero hk hlo⟩
    Fintype.card (ZMod n) = n ∧
    ∃ S : Finset (ZMod n),
      0 ∉ S ∧ (∀ x : ZMod n, x ∈ S ↔ -x ∈ S) ∧
      (SimpleGraph.circulantGraph (S : Set (ZMod n))).CliqueFree 3 ∧
      (SimpleGraph.circulantGraph (S : Set (ZMod n))).IsRegularOfDegree (2 * k + 1) ∧
      (SimpleGraph.circulantGraph (S : Set (ZMod n))).indepNum = 2 * k + 1
```

The [complete expanded type](formalization/MAIN_THEOREM_TYPE.txt) is the actual
recorded output, including implicit parameters and finite instances. The same
existentially quantified `S` supplies every graph property. The parameter range
gives `n >= 8`, so `ZMod n` is finite with exactly `n` vertices; nonzero and finite
instances are derived internally. The written condition `k >= 1` already follows
from the original interval. Both endpoints and both even residue classes modulo
4 are included, without additional construction-parameter assumptions.

All graph differences are taken modulo `n`. With representatives in
`{0,...,n-1}`, the representative of `x-y` for `x<y` is `n+x-y`.
The negative-difference wording in the original Definition 2.1 is read using
this cyclic-group convention. This states the convention used here; it does
not assert that the original authors issued a correction.

mathlib's `circulantGraph S` symmetrizes the difference relation and excludes
self-loops. Because the theorem also proves `0 ∉ S` and `S = -S`, its adjacency
is exactly membership of the modular difference in `S`. `CliqueFree 3` excludes
triangles; `IsRegularOfDegree` gives every vertex's exact degree. On this finite
vertex type, `indepNum` is the **maximum** independent-set size, not merely the
size of an inclusion-maximal independent set.

## Recorded build and axiom scope

[GitHub Actions run 38442507918](https://github.com/Aurantium-47/triangle-free-circulant-existence/actions/runs/38442507918)
completed successfully on 2026-10-13 (UTC), attempt 1, job 115452413854, at source
commit [`01c614aa6e29c0fc88175fca249b17b5cfe65d1d`](https://github.com/Aurantium-47/triangle-free-circulant-existence/commit/01c614aa6e29c0fc88175fca249b17b5cfe65d1d)
and source tree `9aa33777ca0efea32ce8ddb037c5d7dca5387080`.
It used Lean **4.19.0** (commit `6caaee842e94`) and mathlib
`c44e0c8ee63ca166450922a373c7409c5d26b00b`, with the other manifest revisions fixed.

The actual executed checks covered:

- **19 project modules:** 18 `W16` modules and `ImportProbe`, freshly compiled;
  the audit's project imports were matched to those output files.
- **61 declarations:** a complete type and a separate transitive axiom list
  for each, including `W16.exists_agraph`.
- **5 further basic definitions:** `W16.circularGap`, `W16.sortedCircularGap`,
  `W16.parityColor`, `W16.zmodCoordinates`, and `W16.firstConnectionSet` were
  printed in full. They did not each receive a separate `#print axioms` command;
  their dependencies are covered by the final theorem's transitive axiom check.

The final theorem depends on exactly `propext`, `Classical.choice`, and
`Quot.sound`. Every one of the 61 separate axiom lists is a subset of these
standard Lean axioms. No `sorryAx`, native-evaluation axiom or custom axiom
appears in those lists. The [machine-readable run summary](formalization/RUN_38442507918.json)
contains the module/source hashes, all 61 observed lists and the exact counts.
It records an existing run, rather than a new execution of this documentation update.

The [preserved workflow](.github/workflows/w16-circular-gaps-probe.yml) retains
historical names, including “not the full theorem”. Those labels do not describe
the final executed scope above. The tested workflow bytes and all 19 project
sources are preserved. Its exact-commit guards and branch trigger are explained
in [REPRODUCIBILITY.md](REPRODUCIBILITY.md).

## Trust and version boundaries

External precompiled dependency caches are trusted inputs. The successful run
rebuilt the project modules; it did not rebuild all dependencies from source,
replay every dependency or use an independent kernel. The formal type's
connection to the paper is an interpretation of the definitions described
above, not a claim of independent human mathematical review.

The original `main.pdf` and `main.tex` remain the **v0.1.0** manuscript, including
their then-current statement that formalization had not been completed.
This update supplies the later formalization record without altering that
manuscript, its finite-check program, its recorded data, or the existing release.
No new finite computations or PDF build were performed for this update.

This work was prepared with AI assistance. Human expert review and journal peer
review have not been completed. The formalization does not establish bibliographic
priority or prove that no earlier result covers the conjecture.
