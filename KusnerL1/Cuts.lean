import KusnerL1.Clipping
import KusnerL1.Energy
import Mathlib.Algebra.BigOperators.Intervals

/-! Ordered coordinate gaps and their nested prefix cuts. We include one final
zero gap after the last ordered value; this makes the index type `Fin m`.
Removing that zero term gives exactly Definition `def:energies`. -/
namespace KusnerL1
open scoped BigOperators
open Finset

theorem partial_gap_sum (v : ℕ → ℝ) {m i : ℕ} (hi : i ≤ m) :
    (∑ k ∈ range m, (v (k + 1) - v k) * (if k < i then 1 else 0)) = v i - v 0 := by
  rw [← sum_subset (range_mono hi)]
  · calc
      _ = ∑ k ∈ range i, (v (k + 1) - v k) := by
        apply sum_congr rfl
        intro k hk
        simp [mem_range.mp hk]
      _ = _ := sum_range_sub v i
  · intro k hk hki
    simp only [mem_range, not_lt] at hki
    simp [not_lt.mpr hki]

private theorem ordered_distance (v : ℕ → ℝ) (hv : Monotone v) {m i j : ℕ}
    (hi : i ≤ m) (hj : j ≤ m) :
    |v i - v j| = ∑ k ∈ range m, (v (k + 1) - v k) *
      |(if i ≤ k then (1 : ℝ) else 0) - (if j ≤ k then (1 : ℝ) else 0)| := by
  wlog hij : i ≤ j generalizing i j
  · rw [abs_sub_comm]
    simp_rw [abs_sub_comm (if i ≤ _ then (1 : ℝ) else 0)]
    exact this hj hi (by omega)
  have H (k : ℕ) : |(if i ≤ k then (1 : ℝ) else 0) - (if j ≤ k then (1 : ℝ) else 0)| =
      (if k < j then (1 : ℝ) else 0) - (if k < i then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num <;> omega
  simp_rw [H, mul_sub, sum_sub_distrib, partial_gap_sum v hi, partial_gap_sum v hj]
  rw [abs_of_nonpos (sub_nonpos.mpr (hv hij))]
  ring

noncomputable def orderedValue {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ) (k : ℕ) : ℝ :=
  v (order v ⟨min k (m - 1), by omega⟩)

theorem orderedValue_mono {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ) :
    Monotone (orderedValue hm v) := by
  intro i j hij
  apply Tuple.monotone_sort v
  change min i (m - 1) ≤ min j (m - 1)
  exact min_le_min_right _ hij

theorem orderedValue_rank {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ) (i : Fin m) :
    orderedValue hm v ((order v).symm i).val = v i := by
  unfold orderedValue
  have h : min ((order v).symm i).val (m - 1) = ((order v).symm i).val := min_eq_left (by omega)
  simp only [h, Fin.eta, Equiv.apply_symm_apply]

noncomputable def gap {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ) (k : Fin m) : ℝ :=
  orderedValue hm v (k.val + 1) - orderedValue hm v k.val

noncomputable def prefixCut {m : ℕ} (v : Fin m → ℝ) (k : Fin m) : Finset (Fin m) :=
  univ.filter (fun i => ((order v).symm i).val ≤ k.val)

theorem gap_nonneg {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ) (k : Fin m) :
    0 ≤ gap hm v k := sub_nonneg.mpr (orderedValue_mono hm v (Nat.le_succ _))

theorem last_gap_zero {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ) :
    gap hm v ⟨m - 1, by omega⟩ = 0 := by
  simp [gap, orderedValue]

theorem prefixCut_nested {m : ℕ} (v : Fin m → ℝ) {k l : Fin m} (hkl : k ≤ l) :
    prefixCut v k ⊆ prefixCut v l := by
  intro i hi
  simp only [prefixCut, mem_filter, mem_univ, true_and] at hi ⊢
  exact hi.trans hkl

/-- The coordinate nested-cut representation used in Section 3. -/
theorem coordinate_cut_representation {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ) (i l : Fin m) :
    |v i - v l| = ∑ k, gap hm v k * cutDistance (prefixCut v k) i l := by
  have H := ordered_distance (orderedValue hm v) (orderedValue_mono hm v)
    (m := m) (Nat.le_of_lt ((order v).symm i).isLt) (Nat.le_of_lt ((order v).symm l).isLt)
  rw [orderedValue_rank, orderedValue_rank] at H
  rw [H]
  simp only [gap, cutDistance, prefixCut, mem_filter, mem_univ, true_and]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

/-- The span is the sum of the coordinate gaps. -/
theorem sum_gaps {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ) :
    ∑ k, gap hm v k = orderedValue hm v (m - 1) - orderedValue hm v 0 := by
  unfold gap
  rw [Fin.sum_univ_eq_sum_range (fun k => orderedValue hm v (k + 1) - orderedValue hm v k) m, sum_range_sub]
  simp [orderedValue]

section Identities
variable {m n : ℕ} (hm : 0 < m) (y : Fin m → L1 n) (r : Fin m → ℝ)

noncomputable def cutMass (j : Fin n) (k : Fin m) : ℝ :=
  ∑ i ∈ prefixCut (fun i => y i j) k, mass r i

noncomputable def cutEnergy (j : Fin n) : ℝ :=
  ∑ k, gap hm (fun i => y i j) k *
    (cutMass y r j k * (totalMass r - cutMass y r j k) / totalMass r)

/-- Proposition `prop:total-energy`: the cut and pairwise definitions agree. -/
theorem cutEnergy_eq_pairEnergy (hr : ∀ i, 0 < r i) (j : Fin n) :
    cutEnergy hm y r j = pairEnergy y r j := by
  have ht : 0 < totalMass r := by
    let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    exact totalMass_pos r hr
  have H : (∑ i, ∑ l, mass r i * mass r l * |y i j - y l j|) =
      ∑ k, gap hm (fun i => y i j) k *
        (2 * cutMass y r j k * (totalMass r - cutMass y r j k)) := by
    simp_rw [coordinate_cut_representation hm (fun i => y i j), mul_sum]
    rw [sum_comm]
    conv_lhs => arg 2; ext l; rw [sum_comm]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    rw [sum_comm]
    have H := cut_pair_sum (prefixCut (fun i => y i j) k) (mass r)
    dsimp [cutMass, totalMass]
    rw [← H, mul_sum]
    apply sum_congr rfl
    intro i _
    rw [mul_sum]
    apply sum_congr rfl
    intro l _
    ring
  unfold pairEnergy
  rw [H]
  unfold cutEnergy
  rw [sum_div]
  apply sum_congr rfl
  intro k _
  field_simp

/-- The exact total energy in the manuscript's cut definition. -/
theorem total_cutEnergy (hr : ∀ i, 0 < r i) (hs : Star y r) :
    ∑ j, cutEnergy hm y r j = m - 1 := by
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  simp_rw [cutEnergy_eq_pairEnergy hm y r hr]
  simpa using total_pairEnergy y r hr hs

/-- Lemma `lem:weighted-quadratic`, for the actual coordinate prefix cuts. -/
theorem weighted_quadratic (hr : ∀ i, 0 < r i) (hs : Star y r)
    (f : Fin m → ℝ) (hf : ∑ i, mass r i * f i = 0) :
    (∑ j, ∑ k, gap hm (fun i => y i j) k *
      (∑ i ∈ prefixCut (fun i => y i j) k, mass r i * f i) ^ 2) =
        ∑ i, mass r i * f i ^ 2 := by
  have H := weighted_pair_quadratic y r hr hs f hf
  have He (j : Fin n) : (∑ i, ∑ l, mass r i * mass r l * f i * f l * |y i j - y l j|) =
      -2 * ∑ k, gap hm (fun i => y i j) k *
        (∑ i ∈ prefixCut (fun i => y i j) k, mass r i * f i) ^ 2 := by
    simp_rw [coordinate_cut_representation hm (fun i => y i j), mul_sum]
    rw [sum_comm]
    conv_lhs => arg 2; ext l; rw [sum_comm]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    rw [sum_comm]
    have Hc := cut_pair_sum_zero (prefixCut (fun i => y i j) k) (fun i => mass r i * f i) hf
    calc
      _ = gap hm (fun i => y i j) k *
          (∑ i, ∑ l, (mass r i * f i) * (mass r l * f l) *
            cutDistance (prefixCut (fun i => y i j) k) i l) := by
        simp_rw [mul_sum]
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro l _
        ring
      _ = _ := by rw [Hc]; ring
  simp_rw [l1_dist, mul_sum] at H
  rw [sum_comm] at H
  conv_lhs at H => arg 2; ext l; rw [sum_comm]
  rw [sum_comm] at H
  conv_lhs at H => arg 2; ext j; rw [sum_comm]
  simp_rw [He, ← mul_sum] at H
  linarith
/-- The nonnegative-coordinate consequence of the weighted quadratic identity. -/
theorem coordinate_quadratic_le (hr : ∀ i, 0 < r i) (hs : Star y r)
    (f : Fin m → ℝ) (hf : ∑ i, mass r i * f i = 0) (j : Fin n) :
    (∑ k, gap hm (fun i => y i j) k *
      (∑ i ∈ prefixCut (fun i => y i j) k, mass r i * f i) ^ 2) ≤
        ∑ i, mass r i * f i ^ 2 := by
  rw [← weighted_quadratic hm y r hr hs f hf]
  apply Finset.single_le_sum (f := fun j => ∑ k, gap hm (fun i => y i j) k *
    (∑ i ∈ prefixCut (fun i => y i j) k, mass r i * f i) ^ 2)
  · intro j _
    exact sum_nonneg fun k _ => mul_nonneg (gap_nonneg hm _ _) (sq_nonneg _)
  · simp
end Identities

end KusnerL1
