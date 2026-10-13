import W16.FirstTriangleFree

namespace W16

/-- A complete, repetition-free enumeration of the original jump set. -/
theorem firstConnection_enumeration
    {n a r : ℕ} (ha : 1 ≤ a) (hr : r ≤ a - 1) (hn : n = 8 * a + 4 * r) :
    ∃ f : Fin (2 * a + 2 * r + 1) → ZMod n,
      Function.Injective f ∧ Set.range f = firstConnectionSet n a r := by
  classical
  have hn0 : n ≠ 0 := by omega
  letI : NeZero n := ⟨hn0⟩
  have hhalf : n / 2 = 4 * a + 2 * r := by omega
  let p : Fin (2 * a + 2 * r + 1) → ℕ := fun i =>
    if i.val < a then 2 * i.val + 1
    else if i.val < 2 * a then n - (2 * (i.val - a) + 1)
    else 4 * a + 2 * (i.val - 2 * a)
  have hpbound (i : Fin (2 * a + 2 * r + 1)) : p i < n := by
    have hi := i.is_lt
    dsimp [p]
    split_ifs <;> omega
  let f : Fin (2 * a + 2 * r + 1) → ZMod n := fun i => (p i : ZMod n)
  have hval (i : Fin (2 * a + 2 * r + 1)) : (f i).val = p i :=
    ZMod.val_natCast_of_lt (hpbound i)
  have hfi : Function.Injective f := by
    intro i j hij
    have hi := i.is_lt
    have hj := j.is_lt
    have hv : (f i).val = (f j).val := congrArg (fun z : ZMod n => z.val) hij
    rw [hval i, hval j] at hv
    apply Fin.ext
    dsimp [p] at hv
    split_ifs at hv <;> omega
  have hfmem (i : Fin (2 * a + 2 * r + 1)) : f i ∈ firstConnectionSet n a r := by
    have hil := i.is_lt
    by_cases hi : i.val < a
    · refine Or.inl ⟨(i.val : ℤ), by omega, by omega, Or.inl ?_⟩
      simp [f, p, hi]
    · by_cases hi2 : i.val < 2 * a
      · refine Or.inl ⟨((i.val - a : ℕ) : ℤ), by omega, by omega, Or.inr ?_⟩
        have hle : 2 * (i.val - a) + 1 ≤ n := by omega
        simp [f, p, hi, hi2, Nat.cast_sub hle]
      · let j : ℤ := (i.val : ℤ) - 2 * (a : ℤ) - (r : ℤ)
        refine Or.inr ⟨j, by dsimp [j]; omega, by dsimp [j]; omega, ?_⟩
        have heq : ((p i : ℕ) : ℤ) = ((n / 2 : ℕ) : ℤ) + 2 * j := by
          dsimp [p, j]
          rw [if_neg hi, if_neg hi2]
          omega
        have hc := congrArg (fun t : ℤ => (t : ZMod n)) heq
        simpa only [Int.cast_natCast, Int.cast_add, Int.cast_mul, Int.cast_ofNat, f] using hc
  have hsurj (z : ZMod n) (hz : z ∈ firstConnectionSet n a r) : ∃ i, f i = z := by
    have hzlt := ZMod.val_lt z
    have hclass := firstConnection_val_cases ha hr hn z hz
    rcases hclass with ⟨hzp, hzl | hzh⟩ | ⟨hzp, hzl, hzh⟩
    · let i : Fin (2 * a + 2 * r + 1) := ⟨z.val / 2, by omega⟩
      have hi : i.val < a := by dsimp [i]; omega
      have hp : p i = z.val := by
        dsimp [p]
        rw [if_pos hi]
        dsimp [i]
        omega
      refine ⟨i, ?_⟩
      apply ZMod.val_injective n
      rw [hval i, hp]
    · let i : Fin (2 * a + 2 * r + 1) := ⟨a + (n - z.val) / 2, by omega⟩
      have hi : ¬i.val < a := by dsimp [i]; omega
      have hi2 : i.val < 2 * a := by dsimp [i]; omega
      have hp : p i = z.val := by
        dsimp [p]
        rw [if_neg hi, if_pos hi2]
        dsimp [i]
        omega
      refine ⟨i, ?_⟩
      apply ZMod.val_injective n
      rw [hval i, hp]
    · let i : Fin (2 * a + 2 * r + 1) := ⟨2 * a + (z.val - 4 * a) / 2, by omega⟩
      have hi : ¬i.val < a := by dsimp [i]; omega
      have hi2 : ¬i.val < 2 * a := by dsimp [i]; omega
      have hp : p i = z.val := by
        dsimp [p]
        rw [if_neg hi, if_neg hi2]
        dsimp [i]
        omega
      refine ⟨i, ?_⟩
      apply ZMod.val_injective n
      rw [hval i, hp]
  refine ⟨f, hfi, ?_⟩
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact hfmem i
  · exact hsurj z

/-- The actual connection set has a finite representative of the asserted exact cardinality. -/
theorem firstConnection_finset_card
    {n a r : ℕ} (ha : 1 ≤ a) (hr : r ≤ a - 1) (hn : n = 8 * a + 4 * r) :
    ∃ T : Finset (ZMod n), (T : Set (ZMod n)) = firstConnectionSet n a r ∧
      T.card = 2 * a + 2 * r + 1 := by
  classical
  obtain ⟨f, hfi, hfrange⟩ := firstConnection_enumeration ha hr hn
  let T : Finset (ZMod n) := Finset.univ.image f
  refine ⟨T, ?_, ?_⟩
  · rw [← hfrange]
    ext z
    change z ∈ Finset.univ.image f ↔ z ∈ Set.range f
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]
  · change (Finset.univ.image f).card = 2 * a + 2 * r + 1
    rw [Finset.card_image_of_injective _ hfi, Finset.card_univ, Fintype.card_fin]

end W16
