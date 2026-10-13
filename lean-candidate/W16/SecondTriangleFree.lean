import W16.SecondMixedBridge

namespace W16

/-- Actual Q jumps have a short cross-layer representative or a central within-layer representative. -/
theorem secondConnection_val_cases
    {m k t : ℕ} (ht : 2 ≤ t) (htk : t ≤ k) (hkt : k ≤ 2 * t - 2)
    (hm : m = 2 * k + 2 * t - 1) (z : ZMod m × ZMod 2)
    (hz : z ∈ secondConnectionSet m k t) :
    (z.2.val = 1 ∧ (z.1.val ≤ t - 1 ∨ m - (t - 1) ≤ z.1.val)) ∨
    (z.2.val = 0 ∧ 2 * t - 1 ≤ z.1.val ∧ z.1.val ≤ 2 * k) := by
  have hm0 : m ≠ 0 := by omega
  letI : NeZero m := ⟨hm0⟩
  rcases hz with ⟨hs, j, hjlo, hjhi, hjcast⟩ | ⟨hs, j, hjlo, hjhi, hjcast⟩
  · have htag : z.2.val = 1 :=
      (congrArg (fun e : ZMod 2 => e.val) hs).trans (by decide)
    by_cases hj0 : 0 ≤ j
    · have hjm : j < (m : ℤ) := by omega
      have hval : (z.1.val : ℤ) = j := by
        rw [hjcast, ZMod.val_intCast, Int.emod_eq_of_lt hj0 hjm]
      exact Or.inl ⟨htag, Or.inl (by omega)⟩
    · have hcast : z.1 = (((m : ℤ) + j : ℤ) : ZMod m) := by
        rw [hjcast]
        simp only [Int.cast_add, Int.cast_natCast, ZMod.natCast_self, zero_add]
      have h0 : 0 ≤ (m : ℤ) + j := by omega
      have hlt : (m : ℤ) + j < (m : ℤ) := by omega
      have hval : (z.1.val : ℤ) = (m : ℤ) + j := by
        rw [hcast, ZMod.val_intCast, Int.emod_eq_of_lt h0 hlt]
      exact Or.inl ⟨htag, Or.inr (by omega)⟩
  · have htag : z.2.val = 0 :=
      (congrArg (fun e : ZMod 2 => e.val) hs).trans (by decide)
    have hj0 : 0 ≤ j := by omega
    have hjm : j < (m : ℤ) := by omega
    have hval : (z.1.val : ℤ) = j := by
      rw [hjcast, ZMod.val_intCast, Int.emod_eq_of_lt hj0 hjm]
    exact Or.inr ⟨htag, by omega, by omega⟩

/-- Negation preserves both original parts of Q. -/
theorem secondConnection_neg_mem
    {m k t : ℕ} (ht : 2 ≤ t) (htk : t ≤ k) (hkt : k ≤ 2 * t - 2)
    (hm : m = 2 * k + 2 * t - 1) (z : ZMod m × ZMod 2)
    (hz : z ∈ secondConnectionSet m k t) :
    -z ∈ secondConnectionSet m k t := by
  rcases hz with ⟨hs, j, hjlo, hjhi, hjcast⟩ | ⟨hs, j, hjlo, hjhi, hjcast⟩
  · refine Or.inl ⟨?_, -j, by omega, by omega, ?_⟩
    · change -z.2 = 1
      simpa only [hs] using (show -(1 : ZMod 2) = 1 by decide)
    · change -z.1 = ((-j : ℤ) : ZMod m)
      rw [hjcast, Int.cast_neg]
  · refine Or.inr ⟨?_, (m : ℤ) - j, by omega, by omega, ?_⟩
    · change -z.2 = 0
      simpa only [hs] using (neg_zero : -(0 : ZMod 2) = 0)
    · change -z.1 = (((m : ℤ) - j : ℤ) : ZMod m)
      rw [hjcast]
      simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_self, zero_sub]

/-- The original Q has no zero jump. -/
theorem secondConnection_zero_not_mem
    {m k t : ℕ} (ht : 2 ≤ t) (htk : t ≤ k) (hkt : k ≤ 2 * t - 2)
    (hm : m = 2 * k + 2 * t - 1) :
    (0 : ZMod m × ZMod 2) ∉ secondConnectionSet m k t := by
  have hm0 : m ≠ 0 := by omega
  letI : NeZero m := ⟨hm0⟩
  intro hz
  rcases hz with ⟨hs, _⟩ | ⟨_hs, j, hjlo, hjhi, hjcast⟩
  · exact zero_ne_one hs
  · have hj0 : 0 ≤ j := by omega
    have hjm : j < (m : ℤ) := by omega
    have hval : (((j : ZMod m).val) : ℤ) = j := by
      rw [ZMod.val_intCast, Int.emod_eq_of_lt hj0 hjm]
    have heq : (0 : ZMod m) = (j : ZMod m) := hjcast
    have hv0 : (((j : ZMod m).val) : ℤ) = 0 := by
      simp only [← heq, ZMod.val_zero, Nat.cast_zero]
    omega

/-- Two actual Q jumps never sum to a Q jump in the original second-branch range. -/
theorem secondConnection_sum_not_mem
    {m k t : ℕ} (ht : 2 ≤ t) (htk : t ≤ k) (hkt : k ≤ 2 * t - 2)
    (hm : m = 2 * k + 2 * t - 1) (x y : ZMod m × ZMod 2)
    (hx : x ∈ secondConnectionSet m k t) (hy : y ∈ secondConnectionSet m k t) :
    x + y ∉ secondConnectionSet m k t := by
  have hm0 : m ≠ 0 := by omega
  letI : NeZero m := ⟨hm0⟩
  intro hz
  have hxc := secondConnection_val_cases ht htk hkt hm x hx
  have hyc := secondConnection_val_cases ht htk hkt hm y hy
  have hzc := secondConnection_val_cases ht htk hkt hm (x + y) hz
  have hxlt := ZMod.val_lt x.1
  have hylt := ZMod.val_lt y.1
  have hzlt := ZMod.val_lt (x + y).1
  have hsum2 : (x + y).2.val = (x.2.val + y.2.val) % 2 := ZMod.val_add x.2 y.2
  have hsum : (x + y).1.val = x.1.val + y.1.val ∨
      (x + y).1.val + m = x.1.val + y.1.val := by
    by_cases hsmall : x.1.val + y.1.val < m
    · exact Or.inl (ZMod.val_add_of_lt hsmall)
    · exact Or.inr (ZMod.val_add_val_of_le (by omega)).symm
  rcases hxc with ⟨hxp, hxl | hxh⟩ | ⟨hxp, hxl, hxh⟩ <;>
    rcases hyc with ⟨hyp, hyl | hyh⟩ | ⟨hyp, hyl, hyh⟩ <;>
    rcases hzc with ⟨hzp, hzl | hzh⟩ | ⟨hzp, hzl, hzh⟩ <;>
    rcases hsum with hsum | hsum <;> omega

/-- The actual second-construction graph has no three-clique. -/
theorem secondConnection_triangleFree
    {m k t : ℕ} (ht : 2 ≤ t) (htk : t ≤ k) (hkt : k ≤ 2 * t - 2)
    (hm : m = 2 * k + 2 * t - 1) :
    (SimpleGraph.circulantGraph (secondConnectionSet m k t)).CliqueFree 3 := by
  classical
  have hdir {u v : ZMod m × ZMod 2}
      (h : (SimpleGraph.circulantGraph (secondConnectionSet m k t)).Adj u v) :
      v - u ∈ secondConnectionSet m k t := by
    rw [SimpleGraph.circulantGraph_adj] at h
    rcases h.2 with h | h
    · have hneg := secondConnection_neg_mem ht htk hkt hm (u - v) h
      simpa only [neg_sub] using hneg
    · exact h
  intro s hs
  obtain ⟨x, y, z, hxy, hxz, hyz, _hs⟩ := SimpleGraph.is3Clique_iff.mp hs
  have hsum : (y - x) + (z - y) = z - x := by rw [add_comm, sub_add_sub_cancel]
  apply secondConnection_sum_not_mem ht htk hkt hm (y - x) (z - y) (hdir hxy) (hdir hyz)
  rw [hsum]
  exact hdir hxz

end W16
