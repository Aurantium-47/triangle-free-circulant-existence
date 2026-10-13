import W16.FirstIndependentBound

namespace W16

/-- The actual connection set lies in the two short odd ends or the central even interval. -/
theorem firstConnection_val_cases
    {n a r : ℕ} (ha : 1 ≤ a) (hr : r ≤ a - 1) (hn : n = 8 * a + 4 * r)
    (z : ZMod n) (hz : z ∈ firstConnectionSet n a r) :
    (z.val % 2 = 1 ∧ (z.val < 2 * a ∨ n - 2 * a < z.val)) ∨
    (z.val % 2 = 0 ∧ 4 * a ≤ z.val ∧ z.val ≤ n - 4 * a) := by
  have hn0 : n ≠ 0 := by omega
  letI : NeZero n := ⟨hn0⟩
  rcases hz with ⟨k, hk0, hka, heq | heq⟩ | ⟨j, hj0, hjr, heq⟩
  · have h0 : 0 ≤ 2 * k + 1 := by omega
    have hlt : 2 * k + 1 < (n : ℤ) := by omega
    have hval : (z.val : ℤ) = 2 * k + 1 := by
      rw [heq, ZMod.val_intCast, Int.emod_eq_of_lt h0 hlt]
    left
    omega
  · have hcast : z = (((n : ℤ) - (2 * k + 1) : ℤ) : ZMod n) := by
      rw [heq]
      simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_self, zero_sub]
    have h0 : 0 ≤ (n : ℤ) - (2 * k + 1) := by omega
    have hlt : (n : ℤ) - (2 * k + 1) < (n : ℤ) := by omega
    have hval : (z.val : ℤ) = (n : ℤ) - (2 * k + 1) := by
      rw [hcast, ZMod.val_intCast, Int.emod_eq_of_lt h0 hlt]
    left
    omega
  · have hhalf : n / 2 = 4 * a + 2 * r := by omega
    have hcast : z = ((((n / 2 : ℕ) : ℤ) + 2 * j : ℤ) : ZMod n) := by
      rw [heq]
      simp only [Int.cast_add, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat]
    have h0 : 0 ≤ ((n / 2 : ℕ) : ℤ) + 2 * j := by omega
    have hlt : ((n / 2 : ℕ) : ℤ) + 2 * j < (n : ℤ) := by omega
    have hval : (z.val : ℤ) = ((n / 2 : ℕ) : ℤ) + 2 * j := by
      rw [hcast, ZMod.val_intCast, Int.emod_eq_of_lt h0 hlt]
    right
    omega

/-- Negating a jump preserves the original connection set. -/
theorem firstConnection_neg_mem
    {n a r : ℕ} (ha : 1 ≤ a) (hr : r ≤ a - 1) (hn : n = 8 * a + 4 * r)
    (z : ZMod n) (hz : z ∈ firstConnectionSet n a r) :
    -z ∈ firstConnectionSet n a r := by
  rcases hz with ⟨k, hk0, hka, heq | heq⟩ | ⟨j, hj0, hjr, heq⟩
  · exact Or.inl ⟨k, hk0, hka, Or.inr (by rw [heq])⟩
  · exact Or.inl ⟨k, hk0, hka, Or.inl (by rw [heq, neg_neg])⟩
  · have htwice : ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n) = 0 := by
      rw [← Nat.cast_add, show n / 2 + n / 2 = n by omega, ZMod.natCast_self]
    have hneg : -((n / 2 : ℕ) : ZMod n) = ((n / 2 : ℕ) : ZMod n) := by
      calc
        -((n / 2 : ℕ) : ZMod n) =
            -((n / 2 : ℕ) : ZMod n) +
              (((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n)) := by
                rw [htwice, add_zero]
        _ = ((n / 2 : ℕ) : ZMod n) := by
          rw [← add_assoc, neg_add_cancel, zero_add]
    refine Or.inr ⟨-j, by omega, by omega, ?_⟩
    rw [heq, neg_add, hneg, Int.cast_neg, mul_neg]

/-- Zero is not one of the original jumps. -/
theorem firstConnection_zero_not_mem
    {n a r : ℕ} (ha : 1 ≤ a) (hr : r ≤ a - 1) (hn : n = 8 * a + 4 * r) :
    (0 : ZMod n) ∉ firstConnectionSet n a r := by
  intro hz
  have h := firstConnection_val_cases ha hr hn 0 hz
  simp only [ZMod.val_zero] at h
  omega

/-- No sum of two actual jumps is an actual jump in the original parameter range. -/
theorem firstConnection_sum_not_mem
    {n a r : ℕ} (ha : 1 ≤ a) (hr : r ≤ a - 1) (hn : n = 8 * a + 4 * r)
    (x y : ZMod n) (hx : x ∈ firstConnectionSet n a r)
    (hy : y ∈ firstConnectionSet n a r) :
    x + y ∉ firstConnectionSet n a r := by
  have hn0 : n ≠ 0 := by omega
  letI : NeZero n := ⟨hn0⟩
  intro hz
  have hxc := firstConnection_val_cases ha hr hn x hx
  have hyc := firstConnection_val_cases ha hr hn y hy
  have hzc := firstConnection_val_cases ha hr hn (x + y) hz
  have hxlt := ZMod.val_lt x
  have hylt := ZMod.val_lt y
  have hzlt := ZMod.val_lt (x + y)
  have hsum : (x + y).val = x.val + y.val ∨ (x + y).val + n = x.val + y.val := by
    by_cases hsmall : x.val + y.val < n
    · exact Or.inl (ZMod.val_add_of_lt hsmall)
    · exact Or.inr (ZMod.val_add_val_of_le (by omega)).symm
  rcases hxc with ⟨hxp, hxl | hxh⟩ | ⟨hxp, hxl, hxh⟩ <;>
    rcases hyc with ⟨hyp, hyl | hyh⟩ | ⟨hyp, hyl, hyh⟩ <;>
    rcases hzc with ⟨hzp, hzl | hzh⟩ | ⟨hzp, hzl, hzh⟩ <;>
    rcases hsum with hsum | hsum <;> omega

/-- The explicitly defined first circulant construction has no three-clique. -/
theorem firstConnection_triangleFree
    {n a r : ℕ} (ha : 1 ≤ a) (hr : r ≤ a - 1) (hn : n = 8 * a + 4 * r) :
    (SimpleGraph.circulantGraph (firstConnectionSet n a r)).CliqueFree 3 := by
  classical
  have hdir {u v : ZMod n}
      (h : (SimpleGraph.circulantGraph (firstConnectionSet n a r)).Adj u v) :
      v - u ∈ firstConnectionSet n a r := by
    rw [SimpleGraph.circulantGraph_adj] at h
    rcases h.2 with h | h
    · have hneg := firstConnection_neg_mem ha hr hn (u - v) h
      simpa only [neg_sub] using hneg
    · exact h
  intro t ht
  obtain ⟨x, y, z, hxy, hxz, hyz, _ht⟩ := SimpleGraph.is3Clique_iff.mp ht
  have hsum : (y - x) + (z - y) = z - x := by
    rw [add_comm, sub_add_sub_cancel]
  apply firstConnection_sum_not_mem ha hr hn (y - x) (z - y) (hdir hxy) (hdir hyz)
  rw [hsum]
  exact hdir hxz

end W16
