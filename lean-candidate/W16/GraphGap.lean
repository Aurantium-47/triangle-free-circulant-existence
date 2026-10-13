import W16.GapBound
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace W16

/-- Integer representatives of actual modular vertices. -/
def zmodCoordinates {n m : ℕ} (v : Fin (m + 1) → ZMod n) (i : Fin (m + 1)) : ℤ :=
  (v i).val

/-- The original first-branch connection formula L union E. -/
def firstConnectionSet (n a r : ℕ) : Set (ZMod n) :=
  {z | ∃ k : ℤ, 0 ≤ k ∧ k < (a : ℤ) ∧
    (z = ((2 * k + 1 : ℤ) : ZMod n) ∨ z = -((2 * k + 1 : ℤ) : ZMod n))} ∪
  {z | ∃ j : ℤ, -(r : ℤ) ≤ j ∧ j ≤ (r : ℤ) ∧
    z = ((n / 2 : ℕ) : ZMod n) + 2 * (j : ZMod n)}

/-- The wrap correction vanishes modulo n, leaving the actual directed vertex difference. -/
theorem zmod_sortedCircularGap_eq_sub {n m : ℕ} [NeZero n]
    (v : Fin (m + 1) → ZMod n) (i : Fin (m + 1)) :
    (sortedCircularGap (zmodCoordinates v) (n : ℤ) i : ZMod n) =
      v (finRotate (m + 1) i) - v i := by
  by_cases hi : i = Fin.last m
  · simp only [sortedCircularGap, circularGap, zmodCoordinates, if_pos hi,
      Int.cast_add, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val,
      ZMod.natCast_self, add_zero]
  · simp only [sortedCircularGap, circularGap, zmodCoordinates, if_neg hi,
      Int.cast_add, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val,
      Int.cast_zero, add_zero]

/-- Independence in the actual first-branch graph excludes every short positive odd gap. -/
theorem firstConnection_odd_gap_lower_bound {n a r m : ℕ} [NeZero n]
    (hsize : 2 * a ≤ n) (v : Fin (m + 1) → ZMod n)
    (hsorted : StrictMono (zmodCoordinates v))
    (hindep : (SimpleGraph.circulantGraph (firstConnectionSet n a r)).IsIndepSet
      (Set.range v))
    (i : Fin (m + 1))
    (hodd : Odd (sortedCircularGap (zmodCoordinates v) (n : ℤ) i)) :
    2 * (a : ℤ) + 1 ≤ sortedCircularGap (zmodCoordinates v) (n : ℤ) i := by
  let g : ℤ := sortedCircularGap (zmodCoordinates v) (n : ℤ) i
  have hspan : zmodCoordinates v (Fin.last m) - zmodCoordinates v 0 < (n : ℤ) := by
    have hlast := ZMod.val_lt (v (Fin.last m))
    change ((v (Fin.last m)).val : ℤ) - ((v 0).val : ℤ) < (n : ℤ)
    omega
  have hpos : 0 < g := sortedCircularGap_pos hsorted hspan i
  change 2 * (a : ℤ) + 1 ≤ g
  apply le_of_not_gt
  intro hsmall
  change Odd g at hodd
  obtain ⟨k, hk⟩ := hodd
  have hk0 : 0 ≤ k := by omega
  have hka : k < (a : ℤ) := by omega
  have hgn : g < (n : ℤ) := by omega
  have hcast : (g : ZMod n) = v (finRotate (m + 1) i) - v i :=
    zmod_sortedCircularGap_eq_sub v i
  have hnonzero : (g : ZMod n) ≠ 0 := by
    intro hz
    have hmod : g % (n : ℤ) = 0 % (n : ℤ) :=
      (ZMod.intCast_eq_intCast_iff' g 0 n).mp (by simpa only [Int.cast_zero] using hz)
    rw [Int.emod_eq_of_lt (le_of_lt hpos) hgn, Int.zero_emod] at hmod
    exact (ne_of_gt hpos) hmod
  have hne : v i ≠ v (finRotate (m + 1) i) := by
    intro heq
    apply hnonzero
    rw [hcast, heq, sub_self]
  have hmem : v (finRotate (m + 1) i) - v i ∈ firstConnectionSet n a r := by
    apply Or.inl
    refine ⟨k, hk0, hka, Or.inl ?_⟩
    rw [← hcast, hk]
  have hadj : (SimpleGraph.circulantGraph (firstConnectionSet n a r)).Adj
      (v i) (v (finRotate (m + 1) i)) := by
    rw [SimpleGraph.circulantGraph_adj]
    exact ⟨hne, Or.inr hmem⟩
  exact hindep (Set.mem_range_self i) (Set.mem_range_self (finRotate (m + 1) i)) hne hadj

end W16
