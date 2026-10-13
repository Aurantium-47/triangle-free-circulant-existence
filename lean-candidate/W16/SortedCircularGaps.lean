import W16.CircularGaps
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Order.Monotone.Defs

open scoped BigOperators

namespace W16

/-- Gaps in increasing coordinate order, with the last index returning to zero. -/
def sortedCircularGap {m : ℕ} (x : Fin (m + 1) → ℤ)
    (circumference : ℤ) (i : Fin (m + 1)) : ℤ :=
  circularGap (finRotate (m + 1)) x circumference (Fin.last m) i

/-- Strict order gives internal positivity; the span bound gives wrap-around positivity. -/
theorem sortedCircularGap_pos {m : ℕ} {x : Fin (m + 1) → ℤ}
    {circumference : ℤ} (hx : StrictMono x)
    (hspan : x (Fin.last m) - x 0 < circumference) (i : Fin (m + 1)) :
    0 < sortedCircularGap x circumference i := by
  by_cases hi : i = Fin.last m
  · subst i
    change 0 < (x (finRotate (m + 1) (Fin.last m)) - x (Fin.last m)) +
      (if Fin.last m = Fin.last m then circumference else 0)
    rw [finRotate_last, if_pos rfl]
    change 0 < (x 0 - x (Fin.last m)) + circumference
    rw [sub_add_eq_add_sub, add_comm (x 0) circumference]
    exact sub_pos.mpr (sub_lt_iff_lt_add.mp hspan)
  · simpa [sortedCircularGap, circularGap, hi]
      using (sub_pos.mpr (hx ((lt_finRotate_iff_ne_last i).mpr hi)))

/-- The ordered circular gaps are all positive and exhaust exactly one circumference. -/
theorem sortedCircularGaps_pos_sum {m : ℕ} {x : Fin (m + 1) → ℤ}
    {circumference : ℤ} (hx : StrictMono x)
    (hspan : x (Fin.last m) - x 0 < circumference) :
    (∀ i, 0 < sortedCircularGap x circumference i) ∧
      (∑ i : Fin (m + 1), sortedCircularGap x circumference i) = circumference := by
  exact ⟨fun i => sortedCircularGap_pos hx hspan i,
    sum_circularGaps (finRotate (m + 1)) x circumference (Fin.last m)⟩

end W16
