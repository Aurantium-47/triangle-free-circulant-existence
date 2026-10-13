import W16.CyclicStep

namespace W16

/-- Repeatedly adjoining the one-step translate; the membership theorem identifies the actual interval. -/
def cyclicIntervalSum {n : ℕ} (A : Finset (ZMod n)) : ℕ → Finset (ZMod n)
  | 0 => A
  | d + 1 => cyclicIntervalSum A d ∪ (cyclicIntervalSum A d).image (fun x => x + 1)

/-- The recursive finset is exactly the sum with the modular interval from zero through d. -/
theorem mem_cyclicIntervalSum {n : ℕ} (A : Finset (ZMod n)) (d : ℕ) (z : ZMod n) :
    z ∈ cyclicIntervalSum A d ↔
      ∃ a ∈ A, ∃ j : ℕ, j ≤ d ∧ a + (j : ZMod n) = z := by
  classical
  induction d generalizing z with
  | zero => simp [cyclicIntervalSum]
  | succ d ih =>
    simp only [cyclicIntervalSum, Finset.mem_union, Finset.mem_image, ih]
    constructor
    · rintro (⟨a, ha, j, hj, haz⟩ | ⟨b, ⟨a, ha, j, hj, hab⟩, hbz⟩)
      · exact ⟨a, ha, j, by omega, haz⟩
      · refine ⟨a, ha, j + 1, by omega, ?_⟩
        rw [Nat.cast_succ, ← add_assoc, hab]
        exact hbz
    · rintro ⟨a, ha, j, hj, haz⟩
      cases j with
      | zero => exact Or.inl ⟨a, ha, 0, by omega, haz⟩
      | succ j =>
        refine Or.inr ⟨a + (j : ZMod n), ⟨a, ha, j, by omega, rfl⟩, ?_⟩
        simpa only [Nat.cast_succ, ← add_assoc] using haz

/-- A nonempty set expanded by a cyclic interval grows linearly until it fills the cyclic group. -/
theorem card_cyclicIntervalSum_lower {n : ℕ} [NeZero n]
    (A : Finset (ZMod n)) (hne : A.Nonempty) (d : ℕ) :
    min n (A.card + d) ≤ (cyclicIntervalSum A d).card := by
  classical
  obtain ⟨a, ha⟩ := hne
  have hsub (j : ℕ) : A ⊆ cyclicIntervalSum A j := by
    intro x hx
    exact (mem_cyclicIntervalSum A j x).mpr ⟨x, hx, 0, by omega, by simp⟩
  induction d with
  | zero => simpa only [cyclicIntervalSum, Nat.add_zero] using Nat.min_le_right n A.card
  | succ d ih =>
    let B := cyclicIntervalSum A d
    change min n (A.card + d) ≤ B.card at ih
    change min n (A.card + (d + 1)) ≤ (B ∪ B.image (fun x => x + 1)).card
    by_cases hfull : B = Finset.univ
    · have hc : B.card = n := by rw [hfull, Finset.card_univ, ZMod.card]
      have hsubset : B ⊆ B ∪ B.image (fun x => x + 1) := by
        intro x hx
        exact Finset.mem_union.mpr (Or.inl hx)
      have hcard := Finset.card_le_card hsubset
      exact (Nat.min_le_left n (A.card + (d + 1))).trans (by omega)
    · have hBn : B.Nonempty := ⟨a, hsub d ha⟩
      have hcard := zmod_one_step_growth B hBn hfull
      by_cases hk : n ≤ A.card + d
      · rw [Nat.min_eq_left hk] at ih
        exact (Nat.min_le_left n (A.card + (d + 1))).trans (by omega)
      · rw [Nat.min_eq_right (by omega : A.card + d ≤ n)] at ih
        exact (Nat.min_le_right n (A.card + (d + 1))).trans (by omega)

end W16
