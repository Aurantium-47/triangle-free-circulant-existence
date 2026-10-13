import W16.SecondConnectionCard

namespace W16

/-- The actual first-coordinate projection of the vertices in one tagged layer. -/
def secondLayerVertices {m : ℕ} (I : Finset (ZMod m × ZMod 2)) (e : ZMod 2) :
    Finset (ZMod m) :=
  (I.filter (fun p => p.2 = e)).image Prod.fst

open scoped Classical

/-- Membership in the filtered projection is exactly membership of the tagged vertex. -/
theorem mem_secondLayerVertices {m : ℕ} (I : Finset (ZMod m × ZMod 2))
    (e : ZMod 2) (x : ZMod m) :
    x ∈ secondLayerVertices I e ↔ (x, e) ∈ I := by
  classical
  change x ∈ (I.filter (fun p => p.2 = e)).image Prod.fst ↔ (x, e) ∈ I
  constructor
  · intro hx
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hx
    obtain ⟨hpI, hpe⟩ := Finset.mem_filter.mp hp
    have heq : p = (x, e) := Prod.ext hpx hpe
    rw [heq] at hpI
    exact hpI
  · intro hx
    exact Finset.mem_image.mpr ⟨(x, e), Finset.mem_filter.mpr ⟨hx, rfl⟩, rfl⟩

/-- Every finite vertex set is exactly the union of its two actual tagged projections. -/
theorem secondLayer_decomposition {m : ℕ} (I : Finset (ZMod m × ZMod 2)) :
    I = (secondLayerVertices I 0).product ({0} : Finset (ZMod 2)) ∪
      (secondLayerVertices I 1).product ({1} : Finset (ZMod 2)) := by
  classical
  have htwo (e : ZMod 2) : e = 0 ∨ e = 1 := by
    have helt := ZMod.val_lt e
    have hval : e.val = 0 ∨ e.val = 1 := by omega
    rcases hval with h | h
    · exact Or.inl (by simpa only [h, Nat.cast_zero] using (ZMod.natCast_zmod_val e).symm)
    · exact Or.inr (by simpa only [h, Nat.cast_one] using (ZMod.natCast_zmod_val e).symm)
  ext p
  rcases p with ⟨x, e⟩
  rcases htwo e with rfl | rfl <;>
    simp [Finset.product_eq_sprod, Finset.mem_product, mem_secondLayerVertices]

/-- One genuine nonzero U jump gives a half-layer bound without assuming a matching. -/
theorem second_single_layer_independent_card_bound
    {m k t : ℕ} (ht : 2 ≤ t) (htk : t ≤ k) (hkt : k ≤ 2 * t - 2)
    (hm : m = 2 * k + 2 * t - 1) (I : Finset (ZMod m × ZMod 2)) (e : ZMod 2)
    (hindep : (SimpleGraph.circulantGraph (secondConnectionSet m k t)).IsIndepSet
      (I : Set (ZMod m × ZMod 2)))
    (hsame : ∀ p ∈ I, p.2 = e) : 2 * I.card ≤ m := by
  classical
  letI : NeZero m := ⟨secondParameters_ne_zero ht hm⟩
  let c : ZMod m := ((2 * t - 1 : ℕ) : ZMod m)
  have hcval : c.val = 2 * t - 1 := ZMod.val_natCast_of_lt (by omega)
  have hcne : c ≠ 0 := by
    intro hc0
    have hv : c.val = 0 := by simp only [hc0, ZMod.val_zero]
    omega
  let w : ZMod m × ZMod 2 := (c, 0)
  have hwQ : w ∈ secondConnectionSet m k t := by
    refine Or.inr ⟨rfl, 2 * (t : ℤ) - 1, le_rfl, by omega, ?_⟩
    change c = ((2 * (t : ℤ) - 1 : ℤ) : ZMod m)
    have heq : ((2 * t - 1 : ℕ) : ℤ) = 2 * (t : ℤ) - 1 := by omega
    have hcast := congrArg (fun z : ℤ => (z : ZMod m)) heq
    simpa only [c, Int.cast_natCast] using hcast
  let J : Finset (ZMod m × ZMod 2) := I.image (fun p => p + w)
  have hcardJ : J.card = I.card :=
    Finset.card_image_of_injective I (fun _ _ h => add_right_cancel h)
  have hdisj : Disjoint I J := by
    apply Finset.disjoint_left.mpr
    intro y hyI hyJ
    obtain ⟨x, hxI, hxy⟩ := Finset.mem_image.mp hyJ
    change x + w = y at hxy
    have hne : x ≠ y := by
      intro heq
      have hh : x + w = x + 0 := by simpa only [add_zero] using hxy.trans heq.symm
      have hw0 : w = 0 := add_left_cancel hh
      have hc0 : c = 0 := congrArg (fun p : ZMod m × ZMod 2 => p.1) hw0
      exact hcne hc0
    have hdiff : y - x = w := by rw [← hxy, add_sub_cancel_left]
    have hadj : (SimpleGraph.circulantGraph (secondConnectionSet m k t)).Adj x y := by
      rw [SimpleGraph.circulantGraph_adj]
      exact ⟨hne, Or.inr (by rw [hdiff]; exact hwQ)⟩
    exact hindep hxI hyI hne hadj
  have hsub : I ∪ J ⊆ (Finset.univ : Finset (ZMod m)).product ({e} : Finset (ZMod 2)) := by
    intro p hp
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ p.1, Finset.mem_singleton.mpr ?_⟩
    rcases Finset.mem_union.mp hp with hpI | hpJ
    · exact hsame p hpI
    · obtain ⟨x, hxI, hxp⟩ := Finset.mem_image.mp hpJ
      change x + w = p at hxp
      have htag : p.2 = x.2 := by
        calc
          p.2 = (x + w).2 := congrArg (fun q : ZMod m × ZMod 2 => q.2) hxp.symm
          _ = x.2 := by change x.2 + 0 = x.2; exact add_zero _
      exact htag.trans (hsame x hxI)
  have hcardU : ((Finset.univ : Finset (ZMod m)).product ({e} : Finset (ZMod 2))).card = m := by
    simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ,
      ZMod.card, Finset.card_singleton, Nat.mul_one]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hcardJ, hcardU] at hcard
  omega

/-- The original second Q graph bounds every actual independent finset, including empty sets. -/
theorem secondConnection_independent_card_bound
    {m k t : ℕ} (ht : 2 ≤ t) (htk : t ≤ k) (hkt : k ≤ 2 * t - 2)
    (hm : m = 2 * k + 2 * t - 1) (I : Finset (ZMod m × ZMod 2))
    (hindep : (SimpleGraph.circulantGraph (secondConnectionSet m k t)).IsIndepSet
      (I : Set (ZMod m × ZMod 2))) : I.card ≤ 2 * k + 1 := by
  classical
  let A := secondLayerVertices I 0
  let B := secondLayerVertices I 1
  have hdec : I = A.product ({0} : Finset (ZMod 2)) ∪ B.product ({1} : Finset (ZMod 2)) :=
    secondLayer_decomposition I
  by_cases ha : A = ∅
  · have heq : I = B.product ({1} : Finset (ZMod 2)) := by
      simpa only [ha, Finset.product_eq_sprod, Finset.empty_product, Finset.empty_union] using hdec
    have hside : ∀ p ∈ I, p.2 = (1 : ZMod 2) := by
      intro p hp
      rw [heq] at hp
      exact Finset.mem_singleton.mp (Finset.mem_product.mp hp).2
    have hb := second_single_layer_independent_card_bound ht htk hkt hm I 1 hindep hside
    omega
  · by_cases hb : B = ∅
    · have heq : I = A.product ({0} : Finset (ZMod 2)) := by
        simpa only [hb, Finset.product_eq_sprod, Finset.empty_product, Finset.union_empty] using hdec
      have hside : ∀ p ∈ I, p.2 = (0 : ZMod 2) := by
        intro p hp
        rw [heq] at hp
        exact Finset.mem_singleton.mp (Finset.mem_product.mp hp).2
      have hhalf := second_single_layer_independent_card_bound ht htk hkt hm I 0 hindep hside
      omega
    · have hAN : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr ha
      have hBN : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hb
      have htag : (SimpleGraph.circulantGraph (secondConnectionSet m k t)).IsIndepSet
          ((A.product ({0} : Finset (ZMod 2)) : Set (ZMod m × ZMod 2)) ∪
            (B.product ({1} : Finset (ZMod 2)) : Set (ZMod m × ZMod 2))) := by
        intro x hx y hy hne hadj
        apply hindep ?_ ?_ hne hadj
        · rw [hdec]
          exact Finset.mem_union.mpr hx
        · rw [hdec]
          exact Finset.mem_union.mpr hy
      have hbound := second_mixed_independent_card_bound ht htk hkt hm A B hAN hBN htag
      exact (congrArg Finset.card hdec).le.trans hbound

/-- The actual independence number of the product Q graph equals its regular degree. -/
theorem secondConnection_indepNum
    {m k t : ℕ} (ht : 2 ≤ t) (htk : t ≤ k) (hkt : k ≤ 2 * t - 2)
    (hm : m = 2 * k + 2 * t - 1) :
    (SimpleGraph.circulantGraph (secondConnectionSet m k t)).indepNum = 2 * k + 1 := by
  classical
  letI : NeZero m := ⟨secondParameters_ne_zero ht hm⟩
  let G : SimpleGraph (ZMod m × ZMod 2) := SimpleGraph.circulantGraph (secondConnectionSet m k t)
  have htri : G.CliqueFree 3 := secondConnection_triangleFree ht htk hkt hm
  have hN : G.IsIndepSet ((G.neighborFinset (0 : ZMod m × ZMod 2)) : Set (ZMod m × ZMod 2)) := by
    simpa only [SimpleGraph.neighborFinset, Set.coe_toFinset] using
      SimpleGraph.isIndepSet_neighborSet_of_triangleFree G htri (0 : ZMod m × ZMod 2)
  have hlo : (G.neighborFinset (0 : ZMod m × ZMod 2)).card ≤ G.indepNum := hN.card_le_indepNum
  have hdeg : G.degree (0 : ZMod m × ZMod 2) = 2 * k + 1 :=
    secondConnection_regular ht htk hkt hm (0 : ZMod m × ZMod 2)
  rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg] at hlo
  obtain ⟨I, hI⟩ := SimpleGraph.exists_isNIndepSet_indepNum (G := G)
  have hhi := secondConnection_independent_card_bound ht htk hkt hm I hI.isIndepSet
  rw [hI.card_eq] at hhi
  exact Nat.le_antisymm hhi hlo

/-- All size, regularity, triangle and independence properties of the second product construction. -/
theorem secondProductConstruction_properties
    {m k t : ℕ} (ht : 2 ≤ t) (htk : t ≤ k) (hkt : k ≤ 2 * t - 2)
    (hm : m = 2 * k + 2 * t - 1) :
    letI : NeZero m := ⟨secondParameters_ne_zero ht hm⟩
    Fintype.card (ZMod m × ZMod 2) = 2 * m ∧
      (SimpleGraph.circulantGraph (secondConnectionSet m k t)).IsRegularOfDegree (2 * k + 1) ∧
      (SimpleGraph.circulantGraph (secondConnectionSet m k t)).CliqueFree 3 ∧
      (SimpleGraph.circulantGraph (secondConnectionSet m k t)).indepNum = 2 * k + 1 := by
  letI : NeZero m := ⟨secondParameters_ne_zero ht hm⟩
  have hcard : Fintype.card (ZMod m × ZMod 2) = 2 * m := by
    simp only [Fintype.card_prod, ZMod.card, Nat.mul_comm]
  exact ⟨hcard, secondConnection_regular ht htk hkt hm,
    secondConnection_triangleFree ht htk hkt hm, secondConnection_indepNum ht htk hkt hm⟩

end W16
