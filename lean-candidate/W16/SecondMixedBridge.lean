import W16.CyclicInterval
import Mathlib.Data.Finset.Prod

namespace W16

/-- The original second-construction set Q in the two-layer group. -/
def secondConnectionSet (m k t : ℕ) : Set (ZMod m × ZMod 2) :=
  {z | z.2 = 1 ∧ ∃ j : ℤ, -((t - 1 : ℕ) : ℤ) ≤ j ∧
    j ≤ ((t - 1 : ℕ) : ℤ) ∧ z.1 = (j : ZMod m)} ∪
  {z | z.2 = 0 ∧ ∃ j : ℤ, 2 * (t : ℤ) - 1 ≤ j ∧
    j ≤ 2 * (k : ℤ) ∧ z.1 = (j : ZMod m)}

/-- The actual sum with the centered interval from -(t-1) through t-1. -/
def secondCrossSum {m : ℕ} (A : Finset (ZMod m)) (t : ℕ) : Finset (ZMod m) :=
  (cyclicIntervalSum A (2 * t - 2)).image (fun x => x - ((t - 1 : ℕ) : ZMod m))

/-- Actual independence in Q excludes the centered interval sum from the opposite layer. -/
theorem second_cross_sum_disjoint
    {m k t : ℕ} (ht : 2 ≤ t) (htk : t ≤ k) (hkt : k ≤ 2 * t - 2)
    (hm : m = 2 * k + 2 * t - 1) (A B : Finset (ZMod m))
    (hindep : (SimpleGraph.circulantGraph (secondConnectionSet m k t)).IsIndepSet
      ((A.product ({0} : Finset (ZMod 2)) ∪ B.product ({1} : Finset (ZMod 2))) :
        Set (ZMod m × ZMod 2))) :
    Disjoint B (secondCrossSum A t) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hzB hzC
  change z ∈ (cyclicIntervalSum A (2 * t - 2)).image
    (fun x => x - ((t - 1 : ℕ) : ZMod m)) at hzC
  obtain ⟨u, hu, huz⟩ := Finset.mem_image.mp hzC
  change u - ((t - 1 : ℕ) : ZMod m) = z at huz
  obtain ⟨a, ha, j, hj, hau⟩ := (mem_cyclicIntervalSum A (2 * t - 2) u).mp hu
  let q : ℤ := (j : ℤ) - ((t - 1 : ℕ) : ℤ)
  have hd : z - a = (q : ZMod m) := by
    calc
      z - a = (a + (j : ZMod m) - ((t - 1 : ℕ) : ZMod m)) - a := by rw [hau, huz]
      _ = (j : ZMod m) - ((t - 1 : ℕ) : ZMod m) := by
        rw [sub_right_comm, add_sub_cancel_left]
      _ = (q : ZMod m) := by simp only [q, Int.cast_sub, Int.cast_natCast]
  have hmem : (z, (1 : ZMod 2)) - (a, (0 : ZMod 2)) ∈ secondConnectionSet m k t := by
    apply Or.inl
    refine ⟨by simp, q, by dsimp [q]; omega, by dsimp [q]; omega, ?_⟩
    change z - a = (q : ZMod m)
    exact hd
  have hne : (a, (0 : ZMod 2)) ≠ (z, (1 : ZMod 2)) := by
    intro heq
    have hzero : (0 : ZMod 2) = 1 := congrArg (fun p : ZMod m × ZMod 2 => p.2) heq
    exact zero_ne_one hzero
  have hadj : (SimpleGraph.circulantGraph (secondConnectionSet m k t)).Adj
      (a, (0 : ZMod 2)) (z, (1 : ZMod 2)) := by
    rw [SimpleGraph.circulantGraph_adj]
    exact ⟨hne, Or.inr hmem⟩
  have hA : (a, (0 : ZMod 2)) ∈
      A.product ({0} : Finset (ZMod 2)) ∪ B.product ({1} : Finset (ZMod 2)) :=
    Finset.mem_union.mpr (Or.inl (Finset.mem_product.mpr ⟨ha, Finset.mem_singleton_self _⟩))
  have hB : (z, (1 : ZMod 2)) ∈
      A.product ({0} : Finset (ZMod 2)) ∪ B.product ({1} : Finset (ZMod 2)) :=
    Finset.mem_union.mpr (Or.inr (Finset.mem_product.mpr ⟨hzB, Finset.mem_singleton_self _⟩))
  exact hindep (Finset.mem_union.mp hA) (Finset.mem_union.mp hB) hne hadj

/-- The actual tagged union of two nonempty independent layers has at most 2k+1 vertices. -/
theorem second_mixed_independent_card_bound
    {m k t : ℕ} (ht : 2 ≤ t) (htk : t ≤ k) (hkt : k ≤ 2 * t - 2)
    (hm : m = 2 * k + 2 * t - 1) (A B : Finset (ZMod m))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hindep : (SimpleGraph.circulantGraph (secondConnectionSet m k t)).IsIndepSet
      ((A.product ({0} : Finset (ZMod 2)) ∪ B.product ({1} : Finset (ZMod 2))) :
        Set (ZMod m × ZMod 2))) :
    (A.product ({0} : Finset (ZMod 2)) ∪ B.product ({1} : Finset (ZMod 2))).card ≤
      2 * k + 1 := by
  classical
  have hm0 : m ≠ 0 := by omega
  letI : NeZero m := ⟨hm0⟩
  let C := secondCrossSum A t
  have hdisj : Disjoint B C := second_cross_sum_disjoint ht htk hkt hm A B hindep
  have hshift : Function.Injective (fun x : ZMod m => x - ((t - 1 : ℕ) : ZMod m)) := by
    intro x y hxy
    have h := congrArg (fun z : ZMod m => z + ((t - 1 : ℕ) : ZMod m)) hxy
    simpa only [sub_add_cancel] using h
  have hCcard : C.card = (cyclicIntervalSum A (2 * t - 2)).card := by
    change ((cyclicIntervalSum A (2 * t - 2)).image
      (fun x => x - ((t - 1 : ℕ) : ZMod m))).card = _
    exact Finset.card_image_of_injective _ hshift
  have hClower := card_cyclicIntervalSum_lower A hA (2 * t - 2)
  rw [← hCcard] at hClower
  have hcu : (B ∪ C).card ≤ m := by
    have hsub : B ∪ C ⊆ (Finset.univ : Finset (ZMod m)) := by
      intro z _hz
      exact Finset.mem_univ z
    have hcard := Finset.card_le_card hsub
    simpa only [Finset.card_univ, ZMod.card] using hcard
  rw [Finset.card_union_of_disjoint hdisj] at hcu
  have hBpos : 0 < B.card := Finset.card_pos.mpr hB
  have hsum : A.card + (2 * t - 2) ≤ C.card := by
    by_cases hsmall : A.card + (2 * t - 2) ≤ m
    · simpa only [Nat.min_eq_right hsmall] using hClower
    · rw [Nat.min_eq_left (by omega : m ≤ A.card + (2 * t - 2))] at hClower
      omega
  have hprod : Disjoint (A.product ({0} : Finset (ZMod 2)))
      (B.product ({1} : Finset (ZMod 2))) := by
    apply Finset.disjoint_left.mpr
    intro p hpA hpB
    have h0 : p.2 = (0 : ZMod 2) := Finset.mem_singleton.mp (Finset.mem_product.mp hpA).2
    have h1 : p.2 = (1 : ZMod 2) := Finset.mem_singleton.mp (Finset.mem_product.mp hpB).2
    exact zero_ne_one (h0.symm.trans h1)
  simpa only [Finset.card_union_of_disjoint hprod, Finset.card_product,
    Finset.card_singleton, Nat.mul_one] using
    (show A.card + B.card ≤ 2 * k + 1 by omega)

end W16
