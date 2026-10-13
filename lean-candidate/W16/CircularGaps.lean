import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Fintype.Fin

open scoped BigOperators

namespace W16

/-- Coordinate difference with one circumference added at the chosen wrap-around edge. -/
def circularGap {m : ℕ} (next : Equiv.Perm (Fin m)) (x : Fin m → ℤ)
    (circumference : ℤ) (cut i : Fin m) : ℤ :=
  x (next i) - x i + if i = cut then circumference else 0

/-- Summing every edge, including the wrap-around edge, gives one circumference. -/
theorem sum_circularGaps {m : ℕ} (next : Equiv.Perm (Fin m)) (x : Fin m → ℤ)
    (circumference : ℤ) (cut : Fin m) :
    ∑ i : Fin m, circularGap next x circumference cut i = circumference := by
  simp [circularGap, Finset.sum_add_distrib, Finset.sum_sub_distrib, Equiv.sum_comp]

end W16
