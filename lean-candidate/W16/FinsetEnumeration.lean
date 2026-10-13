import W16.GraphGap
import Mathlib.Data.Finset.Sort

namespace W16

/-- Every finite modular vertex set has a complete enumeration in strict representative order. -/
theorem exists_sorted_zmod_enumeration {n : ℕ} [NeZero n]
    (S : Finset (ZMod n)) :
    ∃ v : Fin S.card → ZMod n,
      Set.range v = (S : Set (ZMod n)) ∧
      StrictMono (fun i => ((v i).val : ℤ)) := by
  classical
  let T : Finset ℕ := S.image (fun z : ZMod n => z.val)
  have hcard : T.card = S.card := Finset.card_image_of_injective S (ZMod.val_injective n)
  let e : Fin S.card ↪o ℕ := T.orderEmbOfFin hcard
  have he_mem (i : Fin S.card) : e i ∈ T := T.orderEmbOfFin_mem hcard i
  have he_bound (i : Fin S.card) : e i < n := by
    obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp (he_mem i)
    rw [← heq]
    exact ZMod.val_lt z
  let v : Fin S.card → ZMod n := fun i => (e i : ZMod n)
  have hval (i : Fin S.card) : (v i).val = e i :=
    ZMod.val_natCast_of_lt (he_bound i)
  have hv_mem (i : Fin S.card) : v i ∈ S := by
    obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp (he_mem i)
    have hvz : v i = z := by
      change (e i : ZMod n) = z
      rw [← heq, ZMod.natCast_zmod_val]
    rw [hvz]
    exact hz
  have herange : Set.range (fun i : Fin S.card => e i) = (T : Set ℕ) :=
    Finset.range_orderEmbOfFin T hcard
  have hsurj (z : ZMod n) (hz : z ∈ S) : ∃ i, v i = z := by
    have hzT : z.val ∈ T := Finset.mem_image_of_mem (fun z : ZMod n => z.val) hz
    have hzrange : z.val ∈ Set.range (fun i : Fin S.card => e i) := by
      rw [herange]
      exact hzT
    obtain ⟨i, hi⟩ := hzrange
    refine ⟨i, ?_⟩
    change (e i : ZMod n) = z
    rw [hi, ZMod.natCast_zmod_val]
  refine ⟨v, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact hv_mem i
    · intro hz
      exact hsurj z hz
  · intro i j hij
    change ((v i).val : ℤ) < ((v j).val : ℤ)
    rw [hval i, hval j]
    exact Int.ofNat_lt.mpr (e.strictMono hij)

/-- The gap bound applies to the actual cardinality of every mixed-parity independent finset. -/
theorem firstConnection_mixed_independent_card_bound
    {n a r : ℕ} [NeZero n]
    (ha : 1 ≤ a) (hsize : 2 * a ≤ n) (hc : Even n)
    (S : Finset (ZMod n))
    (hindep : (SimpleGraph.circulantGraph (firstConnectionSet n a r)).IsIndepSet
      (S : Set (ZMod n)))
    (hmixed : ∃ u ∈ S, ∃ w ∈ S, Even (u.val : ℤ) ∧ Odd (w.val : ℤ)) :
    2 * (S.card : ℤ) + 4 * (a : ℤ) - 2 ≤ (n : ℤ) := by
  classical
  obtain ⟨u, hu, w, hw, heu, how⟩ := hmixed
  have huw : u ≠ w := by
    intro heq
    have hew : Even (w.val : ℤ) := by simpa only [heq] using heu
    exact (Int.not_even_iff_odd.mpr how) hew
  have hcard2 : 1 < S.card := Finset.one_lt_card.mpr ⟨u, hu, w, hw, huw⟩
  have hcard_ne : S.card ≠ 0 := by omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hcard_ne
  have hex := exists_sorted_zmod_enumeration S
  rw [hm] at hex
  obtain ⟨v, hvrange, hvmono⟩ := hex
  have hsorted : StrictMono (zmodCoordinates v) := hvmono
  have hIrange : (SimpleGraph.circulantGraph (firstConnectionSet n a r)).IsIndepSet
      (Set.range v) := by
    rw [hvrange]
    exact hindep
  have hu_range : u ∈ Set.range v := by
    rw [hvrange]
    exact hu
  have hw_range : w ∈ Set.range v := by
    rw [hvrange]
    exact hw
  obtain ⟨iu, hiu⟩ := hu_range
  obtain ⟨iw, hiw⟩ := hw_range
  have hmixv : ∃ i j, Even (zmodCoordinates v i) ∧ Odd (zmodCoordinates v j) := by
    refine ⟨iu, iw, ?_, ?_⟩
    · simpa only [zmodCoordinates, hiu] using heu
    · simpa only [zmodCoordinates, hiw] using how
  have hspan : zmodCoordinates v (Fin.last m) - zmodCoordinates v 0 < (n : ℤ) := by
    have hlast := ZMod.val_lt (v (Fin.last m))
    change ((v (Fin.last m)).val : ℤ) - ((v 0).val : ℤ) < (n : ℤ)
    omega
  have hcZ : Even (n : ℤ) := (Int.even_coe_nat n).mpr hc
  have haZ : (1 : ℤ) ≤ (a : ℤ) := by omega
  have hbound := sortedCircularGap_count_bound (zmodCoordinates v) hsorted hspan
    hcZ hmixv haZ (fun i hi => firstConnection_odd_gap_lower_bound hsize v hsorted hIrange i hi)
  simpa only [hm] using hbound

end W16
