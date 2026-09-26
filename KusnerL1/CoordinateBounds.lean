import KusnerL1.SpanTest

/-! Coordinate extrema, positive-gap support, and the endpoint energy bound. -/
namespace KusnerL1
open scoped BigOperators
open Finset Set Real

noncomputable def minValue {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ) : ℝ := orderedValue hm v 0
noncomputable def maxValue {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ) : ℝ := orderedValue hm v (m - 1)
noncomputable def minMass {m : ℕ} (hm : 0 < m) (v μ : Fin m → ℝ) : ℝ :=
  ∑ i ∈ univ.filter (fun i => v i = minValue hm v), μ i
noncomputable def maxMass {m : ℕ} (hm : 0 < m) (v μ : Fin m → ℝ) : ℝ :=
  ∑ i ∈ univ.filter (fun i => v i = maxValue hm v), μ i

lemma minValue_le {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ) (i : Fin m) : minValue hm v ≤ v i := by
  rw [← orderedValue_rank hm v i]
  exact orderedValue_mono hm v (Nat.zero_le _)

lemma le_maxValue {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ) (i : Fin m) : v i ≤ maxValue hm v := by
  rw [← orderedValue_rank hm v i]
  apply orderedValue_mono hm v
  have := ((order v).symm i).isLt
  omega

lemma orderedValue_le_max {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ) (k : ℕ) :
    orderedValue hm v k ≤ maxValue hm v := by
  unfold orderedValue maxValue
  apply Tuple.monotone_sort v
  change min k (m - 1) ≤ min (m - 1) (m - 1)
  simp

lemma minMass_pos {m : ℕ} (hm : 0 < m) (v μ : Fin m → ℝ) (hμ : ∀ i, 0 < μ i) :
    0 < minMass hm v μ := by
  unfold minMass
  apply sum_pos
  · intro i hi; exact hμ i
  · refine ⟨order v ⟨0, hm⟩, ?_⟩
    simp [minValue, orderedValue]

lemma maxMass_pos {m : ℕ} (hm : 0 < m) (v μ : Fin m → ℝ) (hμ : ∀ i, 0 < μ i) :
    0 < maxMass hm v μ := by
  unfold maxMass
  apply sum_pos
  · intro i hi; exact hμ i
  · refine ⟨order v ⟨m - 1, by omega⟩, ?_⟩
    simp [maxValue, orderedValue]

lemma endpointMass_sum_le {m : ℕ} (hm : 0 < m) (v μ : Fin m → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hv : minValue hm v < maxValue hm v) :
    minMass hm v μ + maxMass hm v μ ≤ ∑ i, μ i := by
  unfold minMass maxMass
  rw [sum_filter, sum_filter, ← sum_add_distrib]
  apply sum_le_sum
  intro i _
  split_ifs with h₁ h₂ <;> simp_all

lemma minimum_in_positive_cut {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ) (k : Fin m)
    (hk : 0 < gap hm v k) {i : Fin m} (hi : v i = minValue hm v) : i ∈ prefixCut v k := by
  simp only [prefixCut, Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra H
  have H₁ := orderedValue_mono hm v (show k.val + 1 ≤ ((order v).symm i).val by omega)
  rw [orderedValue_rank, hi] at H₁
  have H₂ := orderedValue_mono hm v (Nat.zero_le k.val)
  dsimp only [gap, minValue] at hk hi H₁
  linarith

lemma maximum_not_in_positive_cut {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ) (k : Fin m)
    (hk : 0 < gap hm v k) {i : Fin m} (hi : v i = maxValue hm v) : i ∉ prefixCut v k := by
  intro H
  simp only [prefixCut, Finset.mem_filter, Finset.mem_univ, true_and] at H
  have H₁ := orderedValue_mono hm v H
  rw [orderedValue_rank, hi] at H₁
  have H₂ := orderedValue_le_max hm v (k.val + 1)
  unfold gap at hk
  linarith

lemma positive_cut_mass_bounds {m : ℕ} (hm : 0 < m) (v μ : Fin m → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (k : Fin m) (hk : 0 < gap hm v k) :
    minMass hm v μ ≤ (∑ i ∈ prefixCut v k, μ i) ∧
      (∑ i ∈ prefixCut v k, μ i) ≤ (∑ i, μ i) - maxMass hm v μ := by
  constructor
  · apply sum_le_sum_of_subset_of_nonneg
    · intro i hi
      exact minimum_in_positive_cut hm v k hk (mem_filter.mp hi).2
    · intro i hi hn; exact hμ i
  · have H : (∑ i ∈ prefixCut v k, μ i) + maxMass hm v μ ≤ ∑ i, μ i := by
      rw [show (∑ i ∈ prefixCut v k, μ i) = ∑ i, if i ∈ prefixCut v k then μ i else 0 by simp,
        maxMass, sum_filter, ← sum_add_distrib]
      apply sum_le_sum
      intro i _
      by_cases hc : i ∈ prefixCut v k
      · have he : v i ≠ maxValue hm v := fun hi => maximum_not_in_positive_cut hm v k hk hi hc
        simp [hc, he]
      · simp [hc]
        split_ifs <;> first | exact le_rfl | exact hμ i
    linarith

lemma cutMass_eq_cumulative {m n : ℕ} (y : Fin m → L1 n) (r : Fin m → ℝ) (j : Fin n) (k : Fin m) :
    cutMass y r j k = cumulative (fun i => y i j) (mass r) (k.val + 1) :=
  sum_prefix _ _ _

/-- Proposition `prop:endpoint-bound` for an arbitrary positive star metric. -/
theorem endpoint_energy_bound {m n : ℕ} (hm : 0 < m) (y : Fin m → L1 n) (r : Fin m → ℝ)
    (hr : ∀ i, 0 < r i) (hs : Star y r) (j : Fin n)
    (hv : minValue hm (fun i => y i j) < maxValue hm (fun i => y i j)) :
    cutEnergy hm y r j ≤ 1 + (1 / 4) *
      log (((totalMass r - minMass hm (fun i => y i j) (mass r)) *
        (totalMass r - maxMass hm (fun i => y i j) (mass r))) /
        (minMass hm (fun i => y i j) (mass r) * maxMass hm (fun i => y i j) (mass r))) := by
  let v := fun i => y i j
  let A := minMass hm v (mass r)
  let B := maxMass hm v (mass r)
  let T := totalMass r
  have hμ : ∀ i, 0 < mass r i := fun i => inv_pos.mpr (hr i)
  have hT : 0 < T := by
    let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    exact totalMass_pos r hr
  have hA : 0 < A := minMass_pos hm v (mass r) hμ
  have hB : 0 < B := maxMass_pos hm v (mass r) hμ
  have hAB : A + B ≤ T := endpointMass_sum_le hm v (mass r) (fun i => (hμ i).le) hv
  obtain ⟨F, E, hF0, hFT, hFE, hFq, hE⟩ := endpoint_test hT hA (by linarith : A ≤ T - B)
    (by linarith : T - B < T)
  have H := coordinate_test_secant hm y r hr hs j F E hF0 hFT hFE
  have Heq : cutEnergy hm y r j = ∑ k : Fin m, gap hm v k *
      F (cumulative v (mass r) (k.val + 1)) ^ 2 := by
    unfold cutEnergy
    apply sum_congr rfl
    intro k _
    rcases (gap_nonneg hm v k).eq_or_lt with hk | hk
    · rw [← hk]
      simp
    · have hc := positive_cut_mass_bounds hm v (mass r) (fun i => (hμ i).le) k hk
      have hc' : cutMass y r j k ∈ Icc A (T - B) := hc
      rw [← cutMass_eq_cumulative, hFq _ hc']
      rfl
  rw [← Heq, hE] at H
  simpa only [sub_sub_cancel] using H

/-- Proposition `prop:span-bound`, including constant coordinates. -/
theorem span_energy_bound {m n : ℕ} (hm : 0 < m) (y : Fin m → L1 n) (r : Fin m → ℝ)
    (hr : ∀ i, 0 < r i) (hs : Star y r) (j : Fin n) {R : ℝ} (hR : 1 < R) :
    cutEnergy hm y r j ≤ a R + b R * totalMass r *
      (maxValue hm (fun i => y i j) - minValue hm (fun i => y i j)) := by
  let d := (R - 1) / (R + 1)
  have hRp : 0 < R + 1 := by linarith
  have hd : 0 < d := div_pos (by linarith) hRp
  have hd1 : d < 1 := (div_lt_one hRp).mpr (by linarith)
  have hT : 0 < totalMass r := by
    let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    exact totalMass_pos r hr
  have hratio : (1 + d) / (1 - d) = R := by
    dsimp [d]
    field_simp
    ring
  have ha : d / 2 * log ((1 + d) / (1 - d)) = a R := by
    rw [hratio]; unfold d a; field_simp
  have hb : spanLambda (totalMass r) d = b R * totalMass r := by
    unfold spanLambda d b
    field_simp
    ring
  obtain ⟨F, E, hF0, hFT, hFE, hFq, hE⟩ := span_test hT hd hd1
  have H := coordinate_test_secant hm y r hr hs j F E hF0 hFT hFE
  rw [hE, ha] at H
  let v := fun i => y i j
  have Hq : cutEnergy hm y r j ≤
      (∑ k : Fin m, gap hm v k * F (cumulative v (mass r) (k.val + 1)) ^ 2) +
        spanLambda (totalMass r) d * (∑ k : Fin m, gap hm v k) := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro k _
    have hc := cumulative_bounds v (mass r) (fun i => (inv_pos.mpr (hr i)).le) (k.val + 1)
    have Hp := mul_le_mul_of_nonneg_left (hFq _ hc) (gap_nonneg hm v k)
    change gap hm v k * q (totalMass r) (cutMass y r j k) ≤ _
    rw [cutMass_eq_cumulative]
    dsimp only [v] at Hp ⊢
    nlinarith only [Hp]
  rw [sum_gaps, hb] at Hq
  change _ ≤ a R + b R * totalMass r * (orderedValue hm v (m - 1) - orderedValue hm v 0)
  linarith

end KusnerL1
