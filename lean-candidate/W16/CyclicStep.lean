import W16.FirstConstruction

namespace W16

/-- A nonempty subset of a finite cyclic group that is closed under one step is the whole group. -/
theorem zmod_step_invariant_eq_univ {n : ℕ} [NeZero n]
    (B : Finset (ZMod n)) (hne : B.Nonempty)
    (hstep : ∀ x ∈ B, x + 1 ∈ B) : B = Finset.univ := by
  classical
  obtain ⟨b, hb⟩ := hne
  have hiter : ∀ j : ℕ, (j : ZMod n) + b ∈ B := by
    intro j
    induction j with
    | zero => simpa only [Nat.cast_zero, zero_add] using hb
    | succ j ih =>
      have hnext := hstep ((j : ZMod n) + b) ih
      simpa only [Nat.cast_succ, add_right_comm] using hnext
  ext z
  simp only [Finset.mem_univ, iff_true]
  simpa only [ZMod.natCast_zmod_val, sub_add_cancel] using hiter (z - b).val

/-- Every nonempty proper cyclic subset gains at least one point when its one-step translate is added. -/
theorem zmod_one_step_growth {n : ℕ} [NeZero n]
    (B : Finset (ZMod n)) (hne : B.Nonempty) (hproper : B ≠ Finset.univ) :
    B.card + 1 ≤ (B ∪ B.image (fun x => x + 1)).card := by
  classical
  have hex : ∃ x ∈ B, x + 1 ∉ B := by
    by_contra h
    push_neg at h
    exact hproper (zmod_step_invariant_eq_univ B hne h)
  obtain ⟨x, hx, hxnot⟩ := hex
  have hins : insert (x + 1) B ⊆ B ∪ B.image (fun x => x + 1) := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
    · exact Finset.mem_union.mpr (Or.inl hy)
  have hcard := Finset.card_le_card hins
  rwa [Finset.card_insert_of_not_mem hxnot] at hcard

end W16
