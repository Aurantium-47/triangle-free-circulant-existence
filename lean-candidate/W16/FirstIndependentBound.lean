import W16.FinsetEnumeration

namespace W16

/-- Antipodal exclusion bounds any independent finset whose representatives have one parity. -/
theorem firstConnection_same_parity_independent_card_bound
    {n a r : ℕ} (ha : 1 ≤ a) (hr : r ≤ a - 1) (hn : n = 8 * a + 4 * r)
    (S : Finset (ZMod n))
    (hindep : (SimpleGraph.circulantGraph (firstConnectionSet n a r)).IsIndepSet
      (S : Set (ZMod n)))
    (hsame : (∀ z ∈ S, Even (z.val : ℤ)) ∨ (∀ z ∈ S, Odd (z.val : ℤ))) :
    S.card ≤ 2 * a + r := by
  classical
  have hn0 : n ≠ 0 := by omega
  letI : NeZero n := ⟨hn0⟩
  let H : ℕ := 4 * a + 2 * r
  have hHpos : 0 < H := by dsimp [H]; omega
  have hnH : n = 2 * H := by dsimp [H]; omega
  have hHM : H = 2 * (2 * a + r) := by dsimp [H]; omega
  have hhalf : n / 2 = H := by omega
  have hanti : ((n / 2 : ℕ) : ZMod n) ∈ firstConnectionSet n a r := by
    apply Or.inr
    exact ⟨(0 : ℤ), by omega, by omega, by simp⟩
  have hnot_antipodal (x : ZMod n) (hx : x ∈ S) (y : ZMod n) (hy : y ∈ S)
      (hxy : x.val + H = y.val) : False := by
    have hne : x ≠ y := by
      intro heq
      have hvals := congrArg (fun z : ZMod n => z.val) heq
      change x.val = y.val at hvals
      omega
    have hadd : x + (H : ZMod n) = y := by
      have hcast := congrArg (fun t : ℕ => (t : ZMod n)) hxy
      simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using hcast
    have hdiff : y - x = ((n / 2 : ℕ) : ZMod n) := by
      rw [← hadd, add_sub_cancel_left, hhalf]
    have hadj : (SimpleGraph.circulantGraph (firstConnectionSet n a r)).Adj x y := by
      rw [SimpleGraph.circulantGraph_adj]
      exact ⟨hne, Or.inr (by rw [hdiff]; exact hanti)⟩
    exact hindep hx hy hne hadj
  let f : ZMod n → ℕ :=
    fun z => if z.val < H then z.val / 2 else (z.val - H) / 2
  have hmap (z : ZMod n) (_hz : z ∈ S) : f z ∈ Finset.range (2 * a + r) := by
    apply Finset.mem_range.mpr
    have hzlt := ZMod.val_lt z
    dsimp [f]
    split_ifs <;> omega
  have hinj : Set.InjOn f (S : Set (ZMod n)) := by
    intro x hx y hy hfeq
    have hxlt := ZMod.val_lt x
    have hylt := ZMod.val_lt y
    have hpar : x.val % 2 = y.val % 2 := by
      rcases hsame with he | ho
      · obtain ⟨kx, hkx⟩ := he x hx
        obtain ⟨ky, hky⟩ := he y hy
        omega
      · obtain ⟨kx, hkx⟩ := ho x hx
        obtain ⟨ky, hky⟩ := ho y hy
        omega
    have hcases : x.val = y.val ∨ x.val + H = y.val ∨ y.val + H = x.val := by
      dsimp [f] at hfeq
      split_ifs at hfeq <;> omega
    rcases hcases with heq | heq | heq
    · exact ZMod.val_injective n heq
    · exact False.elim (hnot_antipodal x hx y hy heq)
    · exact False.elim (hnot_antipodal y hy x hx heq)
  simpa only [Finset.card_range] using
    (Finset.card_le_card_of_injOn (s := S) (t := Finset.range (2 * a + r)) f hmap hinj)

/-- Both parity cases bound every independent finset in the original first construction. -/
theorem firstConnection_independent_card_bound
    {n a r : ℕ} (ha : 1 ≤ a) (hr : r ≤ a - 1) (hn : n = 8 * a + 4 * r)
    (S : Finset (ZMod n))
    (hindep : (SimpleGraph.circulantGraph (firstConnectionSet n a r)).IsIndepSet
      (S : Set (ZMod n))) :
    S.card ≤ 2 * a + 2 * r + 1 := by
  classical
  have hn0 : n ≠ 0 := by omega
  letI : NeZero n := ⟨hn0⟩
  by_cases he : ∀ z ∈ S, Even (z.val : ℤ)
  · have hbound := firstConnection_same_parity_independent_card_bound ha hr hn S hindep
      (Or.inl he)
    omega
  · by_cases ho : ∀ z ∈ S, Odd (z.val : ℤ)
    · have hbound := firstConnection_same_parity_independent_card_bound ha hr hn S hindep
        (Or.inr ho)
      omega
    · push_neg at he ho
      obtain ⟨u, hu, hnu⟩ := he
      obtain ⟨v, hv, hnv⟩ := ho
      have hou : Odd (u.val : ℤ) := Int.not_even_iff_odd.mp hnu
      have hev : Even (v.val : ℤ) := by
        by_contra hnev
        exact hnv (Int.not_even_iff_odd.mp hnev)
      have hsize : 2 * a ≤ n := by omega
      have hc : Even n := ⟨4 * a + 2 * r, by omega⟩
      have hbound := firstConnection_mixed_independent_card_bound ha hsize hc S hindep
        ⟨v, hv, u, hu, hev, hou⟩
      omega

end W16
