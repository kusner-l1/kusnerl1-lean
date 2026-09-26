import KusnerL1.Cuts

/-! The discrete part of Lemma `lem:coordinate-test`. -/
namespace KusnerL1
open scoped BigOperators
open Finset

noncomputable def cumulative {m : ℕ} (v μ : Fin m → ℝ) (k : ℕ) : ℝ :=
  ∑ i : Fin m, if i.val < k then μ (order v i) else 0

@[simp] theorem cumulative_zero {m : ℕ} (v μ : Fin m → ℝ) : cumulative v μ 0 = 0 := by
  simp [cumulative]

theorem cumulative_end {m : ℕ} (v μ : Fin m → ℝ) : cumulative v μ m = ∑ i, μ i := by
  simp only [cumulative, Fin.is_lt, ↓reduceIte]
  exact Equiv.sum_comp (order v) μ

theorem cumulative_succ {m : ℕ} (v μ : Fin m → ℝ) (k : Fin m) :
    cumulative v μ (k.val + 1) - cumulative v μ k.val = μ (order v k) := by
  unfold cumulative
  rw [← sum_sub_distrib]
  have H (i : Fin m) : (if i.val < k.val + 1 then μ (order v i) else 0) -
      (if i.val < k.val then μ (order v i) else 0) = if i = k then μ (order v k) else 0 := by
    by_cases hik : i = k
    · subst i
      simp
    · have : i.val ≠ k.val := fun h => hik (Fin.ext h)
      split_ifs <;> simp_all <;> omega
  simp_rw [H]
  simp

theorem cumulative_bounds {m : ℕ} (v μ : Fin m → ℝ) (hμ : ∀ i, 0 ≤ μ i) (k : ℕ) :
    0 ≤ cumulative v μ k ∧ cumulative v μ k ≤ ∑ i, μ i := by
  constructor
  · apply sum_nonneg
    intro i _
    split_ifs
    · exact hμ _
    · exact le_rfl
  · calc
      cumulative v μ k ≤ ∑ i, μ (order v i) := by
        apply sum_le_sum
        intro i _
        split_ifs <;> first | exact le_rfl | exact hμ _
      _ = _ := Equiv.sum_comp (order v) μ

/-- Reindexing a sum over a coordinate prefix by its sorting permutation. -/
theorem sum_prefix {m : ℕ} (v q : Fin m → ℝ) (k : Fin m) :
    (∑ i ∈ prefixCut v k, q i) =
      ∑ i : Fin m, if i.val < k.val + 1 then q (order v i) else 0 := by
  unfold prefixCut
  rw [sum_filter]
  rw [← Equiv.sum_comp (order v) (fun i => if ((order v).symm i).val ≤ k.val then q i else 0)]
  apply sum_congr rfl
  intro i _
  simp only [Equiv.symm_apply_apply, Nat.lt_add_one_iff]

noncomputable def testSlope {m : ℕ} (v μ : Fin m → ℝ) (F : ℝ → ℝ) (i : Fin m) : ℝ :=
  (F (cumulative v μ (((order v).symm i).val + 1)) -
    F (cumulative v μ ((order v).symm i).val)) / μ i

theorem mass_testSlope {m : ℕ} (v μ : Fin m → ℝ) (F : ℝ → ℝ)
    (hμ : ∀ i, 0 < μ i) (i : Fin m) :
    μ (order v i) * testSlope v μ F (order v i) =
      F (cumulative v μ (i.val + 1)) - F (cumulative v μ i.val) := by
  simp only [testSlope, Equiv.symm_apply_apply]
  exact mul_div_cancel₀ _ (hμ _).ne'

theorem testSlope_mean_zero {m : ℕ} (v μ : Fin m → ℝ) (F : ℝ → ℝ)
    (hμ : ∀ i, 0 < μ i) (hF0 : F 0 = 0) (hFT : F (∑ i, μ i) = 0) :
    ∑ i, μ i * testSlope v μ F i = 0 := by
  rw [← Equiv.sum_comp (order v) (fun i => μ i * testSlope v μ F i)]
  simp_rw [mass_testSlope v μ F hμ]
  rw [Fin.sum_univ_eq_sum_range (fun k => F (cumulative v μ (k + 1)) - F (cumulative v μ k)) m,
    sum_range_sub (fun k => F (cumulative v μ k)), cumulative_end, cumulative_zero, hF0, hFT, sub_self]

theorem testSlope_prefix {m : ℕ} (v μ : Fin m → ℝ) (F : ℝ → ℝ)
    (hμ : ∀ i, 0 < μ i) (hF0 : F 0 = 0) (k : Fin m) :
    (∑ i ∈ prefixCut v k, μ i * testSlope v μ F i) = F (cumulative v μ (k.val + 1)) := by
  rw [sum_prefix]
  simp_rw [mass_testSlope v μ F hμ]
  have H (i : Fin m) : (if i.val < k.val + 1 then
      F (cumulative v μ (i.val + 1)) - F (cumulative v μ i.val) else 0) =
      (F (cumulative v μ (i.val + 1)) - F (cumulative v μ i.val)) *
        (if i.val < k.val + 1 then 1 else 0) := by split_ifs <;> simp
  simp_rw [H]
  rw [Fin.sum_univ_eq_sum_range (fun i => (F (cumulative v μ (i + 1)) - F (cumulative v μ i)) *
    (if i < k.val + 1 then 1 else 0)) m,
    partial_gap_sum (fun i => F (cumulative v μ i)) (by omega), cumulative_zero, hF0, sub_zero]

theorem testSlope_energy {m : ℕ} (v μ : Fin m → ℝ) (F : ℝ → ℝ)
    (hμ : ∀ i, 0 < μ i) :
    (∑ i, μ i * testSlope v μ F i ^ 2) =
      ∑ k : Fin m, (F (cumulative v μ (k.val + 1)) - F (cumulative v μ k.val)) ^ 2 /
        (cumulative v μ (k.val + 1) - cumulative v μ k.val) := by
  rw [← Equiv.sum_comp (order v) (fun i => μ i * testSlope v μ F i ^ 2)]
  apply sum_congr rfl
  intro k _
  rw [cumulative_succ]
  simp only [testSlope, Equiv.symm_apply_apply]
  field_simp [(hμ _).ne']

/-- The first inequality of Lemma `lem:coordinate-test`; no differentiability
is needed for this finite statement. -/
theorem coordinate_test_discrete {m n : ℕ} (hm : 0 < m) (y : Fin m → L1 n) (r : Fin m → ℝ)
    (hr : ∀ i, 0 < r i) (hs : Star y r) (j : Fin n) (F : ℝ → ℝ)
    (hF0 : F 0 = 0) (hFT : F (totalMass r) = 0) :
    (∑ k : Fin m, gap hm (fun i => y i j) k *
      F (cumulative (fun i => y i j) (mass r) (k.val + 1)) ^ 2) ≤
    ∑ k : Fin m, (F (cumulative (fun i => y i j) (mass r) (k.val + 1)) -
      F (cumulative (fun i => y i j) (mass r) k.val)) ^ 2 /
      (cumulative (fun i => y i j) (mass r) (k.val + 1) -
        cumulative (fun i => y i j) (mass r) k.val) := by
  have hμ : ∀ i, 0 < mass r i := fun i => inv_pos.mpr (hr i)
  have H := coordinate_quadratic_le hm y r hr hs
    (testSlope (fun i => y i j) (mass r) F)
    (testSlope_mean_zero _ _ _ hμ hF0 hFT) j
  simp_rw [testSlope_prefix _ _ _ hμ hF0] at H
  rw [testSlope_energy _ _ _ hμ] at H
  exact H

end KusnerL1
