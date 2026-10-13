import W16.FirstConnectionCard

open scoped Classical

namespace W16

/-- The original first-construction parameters give a nonzero modulus. -/
theorem firstParameters_ne_zero
    {n a r : ℕ} (ha : 1 ≤ a) (hn : n = 8 * a + 4 * r) : n ≠ 0 := by
  omega

/-- Every actual neighborhood is a translate of the counted connection finset. -/
theorem firstConnection_regular
    {n a r : ℕ} (ha : 1 ≤ a) (hr : r ≤ a - 1) (hn : n = 8 * a + 4 * r) :
    letI : NeZero n := ⟨firstParameters_ne_zero ha hn⟩
    (SimpleGraph.circulantGraph (firstConnectionSet n a r)).IsRegularOfDegree
      (2 * a + 2 * r + 1) := by
  classical
  letI : NeZero n := ⟨firstParameters_ne_zero ha hn⟩
  let G : SimpleGraph (ZMod n) := SimpleGraph.circulantGraph (firstConnectionSet n a r)
  change ∀ v : ZMod n, G.degree v = 2 * a + 2 * r + 1
  intro v
  obtain ⟨T, hT, hcard⟩ := firstConnection_finset_card ha hr hn
  have hN : G.neighborFinset v = T.image (fun s => s + v) := by
    ext w
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_image]
    constructor
    · intro hadj
      have hmem : w - v ∈ firstConnectionSet n a r := by
        change (SimpleGraph.circulantGraph (firstConnectionSet n a r)).Adj v w at hadj
        rw [SimpleGraph.circulantGraph_adj] at hadj
        rcases hadj.2 with h | h
        · have hneg := firstConnection_neg_mem ha hr hn (v - w) h
          simpa only [neg_sub] using hneg
        · exact h
      refine ⟨w - v, ?_, sub_add_cancel w v⟩
      rw [← hT] at hmem
      exact hmem
    · rintro ⟨s, hs, rfl⟩
      have hsS : s ∈ firstConnectionSet n a r := by
        rw [← hT]
        exact hs
      have hs0 : s ≠ 0 := by
        intro hz
        apply firstConnection_zero_not_mem ha hr hn
        simpa only [hz] using hsS
      change (SimpleGraph.circulantGraph (firstConnectionSet n a r)).Adj v (s + v)
      rw [SimpleGraph.circulantGraph_adj]
      refine ⟨?_, Or.inr ?_⟩
      · intro heq
        have hz : (0 : ZMod n) = s := add_right_cancel (by simpa only [zero_add] using heq)
        exact hs0 hz.symm
      · simpa only [add_sub_cancel_right] using hsS
  change (G.neighborFinset v).card = 2 * a + 2 * r + 1
  rw [hN, Finset.card_image_of_injective _ (fun x y h => add_right_cancel h), hcard]

/-- The neighborhood lower bound matches the previously proved bound on every independent finset. -/
theorem firstConnection_indepNum
    {n a r : ℕ} (ha : 1 ≤ a) (hr : r ≤ a - 1) (hn : n = 8 * a + 4 * r) :
    (SimpleGraph.circulantGraph (firstConnectionSet n a r)).indepNum =
      2 * a + 2 * r + 1 := by
  classical
  letI : NeZero n := ⟨firstParameters_ne_zero ha hn⟩
  let G : SimpleGraph (ZMod n) := SimpleGraph.circulantGraph (firstConnectionSet n a r)
  have htri : G.CliqueFree 3 := firstConnection_triangleFree ha hr hn
  have hN : G.IsIndepSet ((G.neighborFinset (0 : ZMod n)) : Set (ZMod n)) := by
    simpa only [SimpleGraph.neighborFinset, Set.coe_toFinset] using
      SimpleGraph.isIndepSet_neighborSet_of_triangleFree G htri (0 : ZMod n)
  have hlo : (G.neighborFinset (0 : ZMod n)).card ≤ G.indepNum := hN.card_le_indepNum
  have hdeg : G.degree (0 : ZMod n) = 2 * a + 2 * r + 1 :=
    firstConnection_regular ha hr hn (0 : ZMod n)
  rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg] at hlo
  obtain ⟨I, hI⟩ := SimpleGraph.exists_isNIndepSet_indepNum (G := G)
  have hhi := firstConnection_independent_card_bound ha hr hn I hI.isIndepSet
  rw [hI.card_eq] at hhi
  exact Nat.le_antisymm hhi hlo

/-- All required graph properties for the first construction in its original parameter range. -/
theorem firstConstruction_properties
    {n a r : ℕ} (ha : 1 ≤ a) (hr : r ≤ a - 1) (hn : n = 8 * a + 4 * r) :
    letI : NeZero n := ⟨firstParameters_ne_zero ha hn⟩
    Fintype.card (ZMod n) = n ∧
      (SimpleGraph.circulantGraph (firstConnectionSet n a r)).IsRegularOfDegree
        (2 * a + 2 * r + 1) ∧
      (SimpleGraph.circulantGraph (firstConnectionSet n a r)).CliqueFree 3 ∧
      (SimpleGraph.circulantGraph (firstConnectionSet n a r)).indepNum =
        2 * a + 2 * r + 1 := by
  letI : NeZero n := ⟨firstParameters_ne_zero ha hn⟩
  exact ⟨ZMod.card n, firstConnection_regular ha hr hn,
    firstConnection_triangleFree ha hr hn, firstConnection_indepNum ha hr hn⟩

end W16
