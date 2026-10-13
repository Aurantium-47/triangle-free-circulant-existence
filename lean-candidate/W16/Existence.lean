import W16.FirstConstruction
import W16.SecondCyclic

open scoped Classical

namespace W16

/-- The original lower bound supplies the finite nonzero cyclic modulus. -/
theorem w16Parameters_ne_zero {n k : ℕ} (hk : 1 ≤ k)
    (hlo : 6 * k + 2 ≤ n) : n ≠ 0 := by
  omega

/-- Every allowed original parameter pair belongs to one of the two proved constructions. -/
theorem finalParameter_split
    {n k : ℕ} (hk : 1 ≤ k) (he : Even n)
    (hlo : 6 * k + 2 ≤ n) (hhi : n ≤ 8 * k) :
    (∃ a r : ℕ,
      1 ≤ a ∧ r ≤ a - 1 ∧ n = 8 * a + 4 * r ∧ k = a + r) ∨
    (∃ m t : ℕ,
      2 ≤ t ∧ t ≤ k ∧ k ≤ 2 * t - 2 ∧
        m = 2 * k + 2 * t - 1 ∧ n = 2 * m) := by
  have hmod : n % 4 = 0 ∨ n % 4 = 2 := by
    obtain ⟨j, hj⟩ := he
    omega
  rcases hmod with hzero | htwo
  · left
    refine ⟨n / 4 - k, 2 * k - n / 4, ?_, ?_, ?_, ?_⟩ <;> omega
  · right
    refine ⟨2 * (n / 4) + 1, n / 4 + 1 - k, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The full original W16 existence statement, with no construction parameters assumed. -/
theorem exists_agraph
    {n k : ℕ} (hk : 1 ≤ k) (he : Even n)
    (hlo : 6 * k + 2 ≤ n) (hhi : n ≤ 8 * k) :
    letI : NeZero n := ⟨w16Parameters_ne_zero hk hlo⟩
    Fintype.card (ZMod n) = n ∧
    ∃ S : Finset (ZMod n),
      0 ∉ S ∧ (∀ x : ZMod n, x ∈ S ↔ -x ∈ S) ∧
      (SimpleGraph.circulantGraph (S : Set (ZMod n))).CliqueFree 3 ∧
      (SimpleGraph.circulantGraph (S : Set (ZMod n))).IsRegularOfDegree (2 * k + 1) ∧
      (SimpleGraph.circulantGraph (S : Set (ZMod n))).indepNum = 2 * k + 1 := by
  classical
  letI : NeZero n := ⟨w16Parameters_ne_zero hk hlo⟩
  refine ⟨ZMod.card n, ?_⟩
  rcases finalParameter_split hk he hlo hhi with
    ⟨a, r, ha, hr, hn, hka⟩ | ⟨m, t, ht, htk, hkt, hm, hn⟩
  · obtain ⟨S, hS, _hScard⟩ := firstConnection_finset_card ha hr hn
    have hdegree : 2 * a + 2 * r + 1 = 2 * k + 1 := by omega
    refine ⟨S, ?_, ?_, ?_, ?_, ?_⟩
    · change (0 : ZMod n) ∉ (S : Set (ZMod n))
      rw [hS]
      exact firstConnection_zero_not_mem ha hr hn
    · intro x
      change x ∈ (S : Set (ZMod n)) ↔ -x ∈ (S : Set (ZMod n))
      rw [hS]
      constructor
      · exact firstConnection_neg_mem ha hr hn x
      · intro hx
        simpa only [neg_neg] using firstConnection_neg_mem ha hr hn (-x) hx
    · rw [hS]
      exact firstConnection_triangleFree ha hr hn
    · intro v
      have hN : (SimpleGraph.circulantGraph (S : Set (ZMod n))).neighborFinset v =
          (SimpleGraph.circulantGraph (firstConnectionSet n a r)).neighborFinset v := by
        ext w
        simp only [SimpleGraph.mem_neighborFinset]
        rw [hS]
      change ((SimpleGraph.circulantGraph (S : Set (ZMod n))).neighborFinset v).card = 2 * k + 1
      exact (congrArg Finset.card hN).trans ((firstConnection_regular ha hr hn v).trans hdegree)
    · rw [hS]
      exact (firstConnection_indepNum ha hr hn).trans hdegree
  · exact secondCyclicConstruction_exists ht htk hkt hm hn

end W16
