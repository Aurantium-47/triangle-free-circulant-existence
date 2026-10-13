import W16.SortedCircularGaps
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.Push

open scoped BigOperators

namespace W16

/-- Integer labels for the two parity classes. -/
def parityColor (z : ℤ) : ℤ := if Even z then 0 else 1

/-- A nonconstant labeling of the actual finite cycle changes on two distinct edges. -/
theorem exists_two_finRotate_changes {m : ℕ} (f : Fin (m + 1) → ℤ)
    (h : ∃ a b, f a ≠ f b) :
    ∃ i j, i ≠ j ∧ f (finRotate (m + 1) i) ≠ f i ∧
      f (finRotate (m + 1) j) ≠ f j := by
  classical
  have hex : ∃ i, f (finRotate (m + 1) i) ≠ f i := by
    by_contra hn
    push_neg at hn
    have hconst : ∀ i : Fin (m + 1), f i = f 0 := by
      intro i
      induction i using Fin.induction with
      | zero => rfl
      | succ k ih =>
        have hrotate : finRotate (m + 1) k.castSucc = k.succ :=
          finRotate_of_lt k.isLt
        exact (congrArg f hrotate).symm.trans ((hn k.castSucc).trans ih)
    obtain ⟨a, b, hab⟩ := h
    exact hab ((hconst a).trans (hconst b).symm)
  obtain ⟨i, hi⟩ := hex
  have hsum : (∑ j : Fin (m + 1), (f (finRotate (m + 1) j) - f j)) = 0 := by
    simp only [Finset.sum_sub_distrib, Equiv.sum_comp, sub_self]
  have hsecond : ∃ j, j ≠ i ∧ f (finRotate (m + 1) j) ≠ f j := by
    apply Classical.byContradiction
    intro hn
    have hsame (j : Fin (m + 1)) (hji : j ≠ i) :
        f (finRotate (m + 1) j) = f j :=
      Classical.byContradiction (fun hd => hn ⟨j, hji, hd⟩)
    have hsingle : (∑ j : Fin (m + 1), (f (finRotate (m + 1) j) - f j)) =
        f (finRotate (m + 1) i) - f i := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact sub_eq_zero.mpr (hsame j hji)
      · simp
    exact hi (sub_eq_zero.mp (hsingle.symm.trans hsum))
  obtain ⟨j, hji, hj⟩ := hsecond
  exact ⟨i, j, fun hij => hji hij.symm, hi, hj⟩

/-- An even wrap correction preserves the equivalence between odd gaps and color changes. -/
theorem odd_sortedCircularGap_iff_color_change {m : ℕ}
    (x : Fin (m + 1) → ℤ) {circumference : ℤ}
    (hc : Even circumference) (i : Fin (m + 1)) :
    Odd (sortedCircularGap x circumference i) ↔
      parityColor (x (finRotate (m + 1) i)) ≠ parityColor (x i) := by
  have hcolor (a b : ℤ) : parityColor a ≠ parityColor b ↔ ¬ (Even a ↔ Even b) := by
    by_cases ha : Even a <;> by_cases hb : Even b <;> simp [parityColor, ha, hb]
  have hcorrection : Even (if i = Fin.last m then circumference else 0) := by
    split <;> simp_all
  simp only [sortedCircularGap, circularGap, ← Int.not_even_iff_odd,
    Int.even_add, Int.even_sub, hcorrection, iff_true]
  exact (hcolor (x (finRotate (m + 1) i)) (x i)).symm

/-- Mixed parity and an even circumference force at least two odd circular gaps. -/
theorem exists_two_odd_sortedCircularGaps {m : ℕ}
    (x : Fin (m + 1) → ℤ) {circumference : ℤ}
    (hc : Even circumference) (hmixed : ∃ a b, Even (x a) ∧ Odd (x b)) :
    ∃ i j, i ≠ j ∧ Odd (sortedCircularGap x circumference i) ∧
      Odd (sortedCircularGap x circumference j) := by
  obtain ⟨a, b, ha, hb⟩ := hmixed
  have hnb : ¬ Even (x b) := Int.not_even_iff_odd.mpr hb
  have hcolors : ∃ a b, parityColor (x a) ≠ parityColor (x b) :=
    ⟨a, b, by simp [parityColor, ha, hnb]⟩
  obtain ⟨i, j, hij, hi, hj⟩ := exists_two_finRotate_changes (fun k => parityColor (x k)) hcolors
  exact ⟨i, j, hij, (odd_sortedCircularGap_iff_color_change x hc i).mpr hi,
    (odd_sortedCircularGap_iff_color_change x hc j).mpr hj⟩

end W16
