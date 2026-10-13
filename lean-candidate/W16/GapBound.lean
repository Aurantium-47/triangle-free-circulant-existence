import W16.ParityCircularGaps
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

namespace W16

/-- Two distinct odd gaps supply two increments above the baseline gap size two. -/
theorem gap_sum_lower_bound {m : ℕ} (g : Fin (m + 1) → ℤ) {a : ℤ}
    (ha : 1 ≤ a)
    (heven : ∀ i, Even (g i) → 2 ≤ g i)
    (hodd : ∀ i, Odd (g i) → 2 * a + 1 ≤ g i)
    (htwo : ∃ i j, i ≠ j ∧ Odd (g i) ∧ Odd (g j)) :
    2 * ((m + 1 : ℕ) : ℤ) + 4 * a - 2 ≤ ∑ i : Fin (m + 1), g i := by
  have hmin (k : Fin (m + 1)) : 2 ≤ g k := by
    rcases Int.even_or_odd (g k) with he | ho
    · exact heven k he
    · have hk := hodd k ho
      omega
  obtain ⟨i, j, hij, hi, hj⟩ := htwo
  have hbi := hodd i hi
  have hbj := hodd j hj
  have hweight (k : Fin (m + 1)) :
      2 + (if k = i then 2 * a - 1 else 0) +
        (if k = j then 2 * a - 1 else 0) ≤ g k := by
    by_cases hki : k = i
    · subst k
      rw [if_pos rfl, if_neg hij]
      omega
    · by_cases hkj : k = j
      · subst k
        rw [if_neg hki, if_pos rfl]
        omega
      · rw [if_neg hki, if_neg hkj]
        simpa only [add_zero] using hmin k
  have hsum :
      (∑ k : Fin (m + 1),
        (2 + (if k = i then 2 * a - 1 else 0) +
          (if k = j then 2 * a - 1 else 0))) ≤ ∑ k : Fin (m + 1), g k :=
    Finset.sum_le_sum (fun k _ => hweight k)
  simp only [Finset.sum_add_distrib] at hsum
  simp at hsum
  omega

/-- The numerical bound for sorted circular gaps, conditional on the graph's odd-gap bound. -/
theorem sortedCircularGap_count_bound {m : ℕ}
    (x : Fin (m + 1) → ℤ) {circumference a : ℤ}
    (hx : StrictMono x)
    (hspan : x (Fin.last m) - x 0 < circumference)
    (hc : Even circumference)
    (hmixed : ∃ i j, Even (x i) ∧ Odd (x j))
    (ha : 1 ≤ a)
    (hodd : ∀ i, Odd (sortedCircularGap x circumference i) →
      2 * a + 1 ≤ sortedCircularGap x circumference i) :
    2 * ((m + 1 : ℕ) : ℤ) + 4 * a - 2 ≤ circumference := by
  have heven (i : Fin (m + 1)) (he : Even (sortedCircularGap x circumference i)) :
      2 ≤ sortedCircularGap x circumference i := by
    have hp := sortedCircularGap_pos hx hspan i
    obtain ⟨z, hz⟩ := he
    omega
  have hbound := gap_sum_lower_bound (fun i => sortedCircularGap x circumference i)
    ha heven hodd (exists_two_odd_sortedCircularGaps x hc hmixed)
  have hsum := (sortedCircularGaps_pos_sum hx hspan).2
  simpa only [hsum] using hbound

end W16
