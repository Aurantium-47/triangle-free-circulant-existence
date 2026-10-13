import W16.SecondTriangleFree

open scoped Classical

namespace W16

/-- The original second-construction parameters give a nonzero modulus. -/
theorem secondParameters_ne_zero {m k t : ℕ} (ht : 2 ≤ t)
    (hm : m = 2 * k + 2 * t - 1) : m ≠ 0 := by
  omega

/-- A complete repetition-free enumeration of the actual Q jumps. -/
theorem secondConnection_enumeration
    {m k t : ℕ} (ht : 2 ≤ t) (htk : t ≤ k) (hkt : k ≤ 2 * t - 2)
    (hm : m = 2 * k + 2 * t - 1) :
    ∃ f : Fin (2 * k + 1) → ZMod m × ZMod 2,
      Function.Injective f ∧ Set.range f = secondConnectionSet m k t := by
  classical
  letI : NeZero m := ⟨secondParameters_ne_zero ht hm⟩
  let p : Fin (2 * k + 1) → ℕ := fun i =>
    if i.val < t - 1 then m + i.val - (t - 1)
    else if i.val < 2 * t - 1 then i.val - (t - 1)
    else i.val
  have hpbound (i : Fin (2 * k + 1)) : p i < m := by
    have hi := i.is_lt
    dsimp [p]
    split_ifs <;> omega
  let f : Fin (2 * k + 1) → ZMod m × ZMod 2 := fun i =>
    ((p i : ZMod m), if i.val < 2 * t - 1 then 1 else 0)
  have hval (i : Fin (2 * k + 1)) : (f i).1.val = p i :=
    ZMod.val_natCast_of_lt (hpbound i)
  have hval2 (i : Fin (2 * k + 1)) :
      (f i).2.val = if i.val < 2 * t - 1 then 1 else 0 := by
    dsimp [f]
    split_ifs <;> decide
  have hfi : Function.Injective f := by
    intro i j hij
    have hi := i.is_lt
    have hj := j.is_lt
    have hv : (f i).1.val = (f j).1.val :=
      congrArg (fun z : ZMod m × ZMod 2 => z.1.val) hij
    rw [hval i, hval j] at hv
    apply Fin.ext
    dsimp [p] at hv
    split_ifs at hv <;> omega
  have hfmem (i : Fin (2 * k + 1)) : f i ∈ secondConnectionSet m k t := by
    have hil := i.is_lt
    by_cases hi : i.val < 2 * t - 1
    · refine Or.inl ⟨?_, (i.val : ℤ) - ((t - 1 : ℕ) : ℤ), by omega, by omega, ?_⟩
      · change (if i.val < 2 * t - 1 then (1 : ZMod 2) else 0) = 1
        exact if_pos hi
      · change (p i : ZMod m) = (((i.val : ℤ) - ((t - 1 : ℕ) : ℤ) : ℤ) : ZMod m)
        by_cases hlo : i.val < t - 1
        · have heq : ((p i : ℕ) : ℤ) = (m : ℤ) + ((i.val : ℤ) - ((t - 1 : ℕ) : ℤ)) := by
            dsimp [p]
            rw [if_pos hlo]
            omega
          have hc := congrArg (fun z : ℤ => (z : ZMod m)) heq
          simpa only [Int.cast_natCast, Int.cast_add, ZMod.natCast_self, zero_add] using hc
        · have heq : ((p i : ℕ) : ℤ) = (i.val : ℤ) - ((t - 1 : ℕ) : ℤ) := by
            dsimp [p]
            rw [if_neg hlo, if_pos hi]
            omega
          have hc := congrArg (fun z : ℤ => (z : ZMod m)) heq
          simpa only [Int.cast_natCast] using hc
    · refine Or.inr ⟨?_, (i.val : ℤ), by omega, by omega, ?_⟩
      · change (if i.val < 2 * t - 1 then (1 : ZMod 2) else 0) = 0
        exact if_neg hi
      · have hlo : ¬i.val < t - 1 := by omega
        change (p i : ZMod m) = ((i.val : ℤ) : ZMod m)
        simp only [p, if_neg hlo, if_neg hi, Int.cast_natCast]
  have hsurj (z : ZMod m × ZMod 2) (hz : z ∈ secondConnectionSet m k t) :
      ∃ i, f i = z := by
    have hzlt := ZMod.val_lt z.1
    have hcases := secondConnection_val_cases ht htk hkt hm z hz
    rcases hcases with ⟨hs, hlo | hhi⟩ | ⟨hs, hlo, hhi⟩
    · let i : Fin (2 * k + 1) := ⟨z.1.val + (t - 1), by omega⟩
      have hi0 : ¬i.val < t - 1 := by dsimp [i]; omega
      have hi : i.val < 2 * t - 1 := by dsimp [i]; omega
      have hp : p i = z.1.val := by
        dsimp [p]
        rw [if_neg hi0, if_pos hi]
        dsimp [i]
        omega
      refine ⟨i, ?_⟩
      apply Prod.ext
      · apply ZMod.val_injective m
        rw [hval i, hp]
      · apply ZMod.val_injective 2
        rw [hval2 i, if_pos hi]
        exact hs.symm
    · let i : Fin (2 * k + 1) := ⟨z.1.val + (t - 1) - m, by omega⟩
      have hi0 : i.val < t - 1 := by dsimp [i]; omega
      have hi : i.val < 2 * t - 1 := by dsimp [i]; omega
      have hp : p i = z.1.val := by
        dsimp [p]
        rw [if_pos hi0]
        dsimp [i]
        omega
      refine ⟨i, ?_⟩
      apply Prod.ext
      · apply ZMod.val_injective m
        rw [hval i, hp]
      · apply ZMod.val_injective 2
        rw [hval2 i, if_pos hi]
        exact hs.symm
    · let i : Fin (2 * k + 1) := ⟨z.1.val, by omega⟩
      have hi0 : ¬i.val < t - 1 := by dsimp [i]; omega
      have hi : ¬i.val < 2 * t - 1 := by dsimp [i]; omega
      have hp : p i = z.1.val := by simp only [p, if_neg hi0, if_neg hi, i]
      refine ⟨i, ?_⟩
      apply Prod.ext
      · apply ZMod.val_injective m
        rw [hval i, hp]
      · apply ZMod.val_injective 2
        rw [hval2 i, if_neg hi]
        exact hs.symm
  refine ⟨f, hfi, ?_⟩
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact hfmem i
  · exact hsurj z

/-- A finite representative of Q has exactly 2k+1 elements. -/
theorem secondConnection_finset_card
    {m k t : ℕ} (ht : 2 ≤ t) (htk : t ≤ k) (hkt : k ≤ 2 * t - 2)
    (hm : m = 2 * k + 2 * t - 1) :
    ∃ T : Finset (ZMod m × ZMod 2), (T : Set (ZMod m × ZMod 2)) =
      secondConnectionSet m k t ∧ T.card = 2 * k + 1 := by
  classical
  obtain ⟨f, hfi, hfrange⟩ := secondConnection_enumeration ht htk hkt hm
  let T : Finset (ZMod m × ZMod 2) := Finset.univ.image f
  refine ⟨T, ?_, ?_⟩
  · rw [← hfrange]
    ext z
    change z ∈ Finset.univ.image f ↔ z ∈ Set.range f
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]
  · change (Finset.univ.image f).card = 2 * k + 1
    rw [Finset.card_image_of_injective _ hfi, Finset.card_univ, Fintype.card_fin]

/-- Every actual Q-neighborhood is a translate of the counted jump finset. -/
theorem secondConnection_regular
    {m k t : ℕ} (ht : 2 ≤ t) (htk : t ≤ k) (hkt : k ≤ 2 * t - 2)
    (hm : m = 2 * k + 2 * t - 1) :
    letI : NeZero m := ⟨secondParameters_ne_zero ht hm⟩
    (SimpleGraph.circulantGraph (secondConnectionSet m k t)).IsRegularOfDegree (2 * k + 1) := by
  classical
  letI : NeZero m := ⟨secondParameters_ne_zero ht hm⟩
  let G : SimpleGraph (ZMod m × ZMod 2) := SimpleGraph.circulantGraph (secondConnectionSet m k t)
  change ∀ v : ZMod m × ZMod 2, G.degree v = 2 * k + 1
  intro v
  obtain ⟨T, hT, hcard⟩ := secondConnection_finset_card ht htk hkt hm
  have hN : G.neighborFinset v = T.image (fun s => s + v) := by
    ext w
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_image]
    constructor
    · intro hadj
      have hmem : w - v ∈ secondConnectionSet m k t := by
        change (SimpleGraph.circulantGraph (secondConnectionSet m k t)).Adj v w at hadj
        rw [SimpleGraph.circulantGraph_adj] at hadj
        rcases hadj.2 with h | h
        · have hneg := secondConnection_neg_mem ht htk hkt hm (v - w) h
          simpa only [neg_sub] using hneg
        · exact h
      refine ⟨w - v, ?_, sub_add_cancel w v⟩
      rw [← hT] at hmem
      exact hmem
    · rintro ⟨s, hs, rfl⟩
      have hsQ : s ∈ secondConnectionSet m k t := by rw [← hT]; exact hs
      have hs0 : s ≠ 0 := by
        intro hz
        apply secondConnection_zero_not_mem ht htk hkt hm
        simpa only [hz] using hsQ
      change (SimpleGraph.circulantGraph (secondConnectionSet m k t)).Adj v (s + v)
      rw [SimpleGraph.circulantGraph_adj]
      refine ⟨?_, Or.inr ?_⟩
      · intro heq
        have hz : (0 : ZMod m × ZMod 2) = s := add_right_cancel (by simpa only [zero_add] using heq)
        exact hs0 hz.symm
      · simpa only [add_sub_cancel_right] using hsQ
  change (G.neighborFinset v).card = 2 * k + 1
  rw [hN, Finset.card_image_of_injective _ (fun x y h => add_right_cancel h), hcard]

end W16
