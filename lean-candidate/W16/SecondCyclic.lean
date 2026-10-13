import W16.SecondIndependent

open scoped Classical

namespace W16

/-- An additive equivalence transports the actual difference-based circulant adjacency. -/
def circulantPreimageIso {A B : Type} [AddGroup A] [AddGroup B]
    (e : A ≃+ B) (Q : Set B) :
    SimpleGraph.circulantGraph (e ⁻¹' Q) ≃g SimpleGraph.circulantGraph Q :=
  { e.toEquiv with
    map_rel_iff' := by
      intro x y
      simp only [SimpleGraph.circulantGraph_adj, Set.mem_preimage, map_sub]
      exact and_congr (not_congr e.injective.eq_iff) Iff.rfl }

/-- A graph isomorphism sends every maximum finite independent set to one of the same size. -/
theorem graphIso_indepNum_le {A B : Type} [Fintype A] [Fintype B]
    {G : SimpleGraph A} {H : SimpleGraph B} (e : G ≃g H) :
    G.indepNum ≤ H.indepNum := by
  classical
  obtain ⟨I, hI⟩ := SimpleGraph.exists_isNIndepSet_indepNum (G := G)
  have hJ : H.IsIndepSet ((I.image e) : Set B) := by
    intro x hx y hy hne hadj
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact hI.isIndepSet hu hv (fun h => hne (congrArg e h)) (e.map_adj_iff.mp hadj)
  have hcard := hJ.card_le_indepNum
  rw [Finset.card_image_of_injective _ e.injective, hI.card_eq] at hcard
  exact hcard

/-- The actual independence number is invariant under a finite graph isomorphism. -/
theorem graphIso_indepNum_eq {A B : Type} [Fintype A] [Fintype B]
    {G : SimpleGraph A} {H : SimpleGraph B} (e : G ≃g H) :
    G.indepNum = H.indepNum := by
  exact Nat.le_antisymm (graphIso_indepNum_le e) (graphIso_indepNum_le e.symm)

/-- The original second modulus is odd, hence coprime to two. -/
theorem secondParameters_coprime_two {m k t : ℕ} (ht : 2 ≤ t)
    (hm : m = 2 * k + 2 * t - 1) : m.Coprime 2 := by
  apply Nat.coprime_two_right.mpr
  exact ⟨k + t - 1, by omega⟩

/-- The cyclic modulus is nonzero as a consequence of the original parameters. -/
theorem secondCyclicParameters_ne_zero {n m k t : ℕ} (ht : 2 ≤ t)
    (hm : m = 2 * k + 2 * t - 1) (hn : n = 2 * m) : n ≠ 0 := by
  have hm0 := secondParameters_ne_zero ht hm
  omega

/-- The exact CRT additive equivalence, with the factor order recorded explicitly. -/
def secondCyclicEquiv {n m k t : ℕ} (ht : 2 ≤ t)
    (hm : m = 2 * k + 2 * t - 1) (hn : n = 2 * m) :
    ZMod n ≃+ (ZMod m × ZMod 2) :=
  ((ZMod.ringEquivCongr (show n = m * 2 by omega)).trans
    (ZMod.chineseRemainder (secondParameters_coprime_two ht hm))).toAddEquiv

/-- CRT preserves the full vertex cardinality of the product construction. -/
theorem secondCyclic_vertex_card {n m k t : ℕ} (ht : 2 ≤ t)
    (hm : m = 2 * k + 2 * t - 1) (hn : n = 2 * m) :
    letI : NeZero n := ⟨secondCyclicParameters_ne_zero ht hm hn⟩
    Fintype.card (ZMod n) = 2 * m := by
  letI : NeZero n := ⟨secondCyclicParameters_ne_zero ht hm hn⟩
  letI : NeZero m := ⟨secondParameters_ne_zero ht hm⟩
  calc
    Fintype.card (ZMod n) = Fintype.card (ZMod m × ZMod 2) :=
      Fintype.card_congr (secondCyclicEquiv ht hm hn).toEquiv
    _ = 2 * m := by simp only [Fintype.card_prod, ZMod.card, Nat.mul_comm]

/-- The original product Q construction gives a genuine cyclic connection finset. -/
theorem secondCyclicConstruction_exists
    {n m k t : ℕ} (ht : 2 ≤ t) (htk : t ≤ k) (hkt : k ≤ 2 * t - 2)
    (hm : m = 2 * k + 2 * t - 1) (hn : n = 2 * m) :
    letI : NeZero n := ⟨secondCyclicParameters_ne_zero ht hm hn⟩
    ∃ S : Finset (ZMod n),
      0 ∉ S ∧ (∀ x : ZMod n, x ∈ S ↔ -x ∈ S) ∧
      (SimpleGraph.circulantGraph (S : Set (ZMod n))).CliqueFree 3 ∧
      (SimpleGraph.circulantGraph (S : Set (ZMod n))).IsRegularOfDegree (2 * k + 1) ∧
      (SimpleGraph.circulantGraph (S : Set (ZMod n))).indepNum = 2 * k + 1 := by
  classical
  letI : NeZero n := ⟨secondCyclicParameters_ne_zero ht hm hn⟩
  letI : NeZero m := ⟨secondParameters_ne_zero ht hm⟩
  let e := secondCyclicEquiv ht hm hn
  let Q := secondConnectionSet m k t
  let S : Finset (ZMod n) := (e ⁻¹' Q).toFinset
  have hS : (S : Set (ZMod n)) = e ⁻¹' Q := Set.coe_toFinset _
  let G := SimpleGraph.circulantGraph (e ⁻¹' Q)
  let H := SimpleGraph.circulantGraph Q
  let eG : G ≃g H := circulantPreimageIso e Q
  have htri : G.CliqueFree 3 :=
    (secondConnection_triangleFree ht htk hkt hm).comap eG.toEmbedding
  have hreg : G.IsRegularOfDegree (2 * k + 1) := by
    intro v
    have hd : G.degree v = H.degree (eG v) := by
      rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
      exact Fintype.card_congr (eG.mapNeighborSet v)
    exact hd.trans (secondConnection_regular ht htk hkt hm (eG v))
  have hind : G.indepNum = 2 * k + 1 :=
    (graphIso_indepNum_eq eG).trans (secondConnection_indepNum ht htk hkt hm)
  refine ⟨S, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [S, Set.mem_toFinset, Set.mem_preimage, map_zero] using
      (secondConnection_zero_not_mem ht htk hkt hm)
  · intro x
    simp only [S, Set.mem_toFinset, Set.mem_preimage, map_neg]
    constructor
    · exact secondConnection_neg_mem ht htk hkt hm (e x)
    · intro hx
      simpa only [neg_neg] using secondConnection_neg_mem ht htk hkt hm (-(e x)) hx
  · rw [hS]
    exact htri
  · intro v
    have hN : (SimpleGraph.circulantGraph (S : Set (ZMod n))).neighborFinset v =
        G.neighborFinset v := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset]
      change (SimpleGraph.circulantGraph (S : Set (ZMod n))).Adj v w ↔
        (SimpleGraph.circulantGraph (e ⁻¹' Q)).Adj v w
      rw [hS]
    change ((SimpleGraph.circulantGraph (S : Set (ZMod n))).neighborFinset v).card = 2 * k + 1
    exact (congrArg Finset.card hN).trans (hreg v)
  · rw [hS]
    exact hind

end W16
