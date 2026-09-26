import KusnerL1.ResidualAccounting
import Mathlib.Analysis.Convex.Jensen

/-! The two averaging arguments of Section 5. -/
namespace KusnerL1
open scoped BigOperators
open Finset Real

lemma sum_ends {n : ℕ} (f : Fin n → ℝ) : (∑ e : Fin n × Bool, f e.1) = 2 * ∑ j, f j := by
  simp [Fintype.sum_prod_type, two_mul, sum_add_distrib]

lemma span_majorant {M u L : ℝ} (hM : 0 < M) (hu : 0 < u) (huM : u ≤ M)
    (hL : L ≤ 1 / u) (hL' : L ≤ 2 / M) : M * L ≤ h (u / M) := by
  apply le_min
  · simpa only [mul_comm] using (le_div_iff₀ hM).mp hL'
  · by_cases hhalf : 2 * u ≤ M
    · have H₁ := (le_div_iff₀ hM).mp hL'
      have H₂ : 2 * (u / M) ≤ 1 := by
        have H := (div_le_one hM).mpr hhalf
        simpa only [mul_div_assoc] using H
      nlinarith
    · have H₁ := (le_div_iff₀ hu).mp hL
      have H₂ := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 2 * u - M) (sub_nonpos.mpr huM)
      have H₃ : M / u ≤ 3 - 2 * (u / M) := by
        apply (div_le_iff₀ hu).mpr
        apply (mul_le_mul_iff_left₀ hM).mp
        field_simp
        nlinarith
      exact (mul_le_mul_of_nonneg_left hL hM.le).trans (by simpa [div_eq_mul_inv] using H₃)

/-- The Jensen step for the minimum of the two affine functions defining `h`. -/
lemma h_sum_le {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    (∑ i, h (v i)) ≤ min (2 * (Fintype.card ι : ℝ))
      (3 * (Fintype.card ι : ℝ) - 2 * ∑ i, v i) := by
  apply le_min
  · have H := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => min_le_left (2 : ℝ) (3 - 2 * v i))
    simpa [h, mul_comm] using H
  · have H := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => min_le_right (2 : ℝ) (3 - 2 * v i))
    simpa [h, sum_sub_distrib, sum_mul, mul_sum, mul_comm] using H

/-- Proposition `prop:average-span`, using precisely the endpoint span and
mass-accounting inequalities. -/
theorem average_span {n : ℕ} (hn : 0 < n) (u : Fin n × Bool → ℝ) (L : Fin n → ℝ)
    {T M z : ℝ} (hT : 0 ≤ T) (hM : 0 < M) (_hz : 2 ≤ z) (hzM : z ≤ M)
    (hu : ∀ e, 0 < u e ∧ u e ≤ M) (huSum : ∑ e, u e = 2 * n * z)
    (haccount : T ≤ 2 * n * z + 2)
    (hspan : ∀ e, L e.1 ≤ 1 / u e) (hmax : ∀ j, L j ≤ 2 / M) :
    T / n * (∑ j, L j) ≤ Phi n M (z / M) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have H := sum_le_sum (fun e (_ : e ∈ (univ : Finset (Fin n × Bool))) =>
    span_majorant hM (hu e).1 (hu e).2 (hspan e) (hmax e.1))
  rw [← mul_sum, sum_ends] at H
  have Hj := h_sum_le (fun e => u e / M)
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.cast_mul,
    Nat.cast_ofNat, ← sum_div, huSum] at Hj
  have H₁ := H.trans (Hj.trans (min_le_left _ _))
  have H₂ := H.trans (Hj.trans (min_le_right _ _))
  simp only [mul_div_assoc] at H₂
  have Hh : M / n * (∑ j, L j) ≤ h (z / M) := by
    rw [show M / n * (∑ j, L j) = M * (∑ j, L j) / n by ring]
    apply le_min
    · apply (div_le_iff₀ hnR).mpr
      nlinarith
    · apply (div_le_iff₀ hnR).mpr
      nlinarith
  have hhp : 0 ≤ h (z / M) := by
    apply le_min (by norm_num)
    have : z / M ≤ 1 := (div_le_one hM).mpr hzM
    linarith
  have Hq := mul_le_mul_of_nonneg_left Hh (div_nonneg hT hM.le)
  have Ht := mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right hM).mpr haccount) hhp
  have heq : T / M * (M / n * (∑ j, L j)) = T / n * (∑ j, L j) := by field_simp
  rw [heq] at Hq
  apply Hq.trans
  convert Ht using 1
  unfold Phi
  ring

lemma log_sum_le {ι : Type*} [Fintype ι] [Nonempty ι] (v : ι → ℝ) (hv : ∀ i, 0 < v i) :
    (∑ i, log (v i)) / Fintype.card ι ≤ log ((∑ i, v i) / Fintype.card ι) := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have H := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := univ) (w := fun _ : ι => (Fintype.card ι : ℝ)⁻¹) (p := v)
    (fun _ _ => inv_nonneg.mpr hN.le) (by simp [hN.ne']) (fun i _ => hv i)
  simpa only [smul_eq_mul, ← div_eq_inv_mul, ← sum_div] using H

/-- The numerator Jensen estimate and denominator chord estimate in
Proposition `prop:average-endpoint`. -/
theorem average_endpoint_logs {n : ℕ} (hn : 0 < n) (u : Fin n × Bool → ℝ)
    {T M z : ℝ} (hu : ∀ e, 2 ≤ u e ∧ u e ≤ M)
    (huSum : ∑ e, u e = 2 * n * z) (_hz : 2 ≤ z)
    (haccount : T ≤ 2 * n * z + 2) (hpos : ∀ e, 0 < T - u e - 2) :
    (∑ e, (log (T - u e - 2) - log (u e + 2))) / (2 * n) ≤ G n M z := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have Hnum := log_sum_le (fun e => T - u e - 2) hpos
  have hsum : (∑ e, (T - u e - 2)) = (2 * n : ℝ) * (T - z - 2) := by
    simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, huSum]
    ring
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.cast_mul,
    Nat.cast_ofNat, hsum] at Hnum
  have hden : (2 * n : ℝ) ≠ 0 := by positivity
  have hmean : (2 * n : ℝ) * (T - z - 2) / (n * 2) = T - z - 2 := by field_simp
  rw [hmean] at Hnum
  have hmpos : 0 < T - z - 2 := by
    have H := sum_pos (fun e (_ : e ∈ (univ : Finset (Fin n × Bool))) => hpos e) univ_nonempty
    rw [hsum] at H
    nlinarith
  have Hlog : log (T - z - 2) ≤ log ((2 * n - 1) * z) := by
    apply log_le_log hmpos
    nlinarith
  have Hden := sum_le_sum (fun e (_ : e ∈ (univ : Finset (Fin n × Bool))) =>
    logarithmic_chord (hu e).1 (hu e).2)
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat, nsmul_eq_mul, ← sum_mul, sum_sub_distrib,
    huSum] at Hden
  have Hnum' := (div_le_iff₀ (by positivity : (0 : ℝ) < n * 2)).mp (Hnum.trans Hlog)
  unfold G
  rw [log_div (by nlinarith : (2 * n - 1 : ℝ) * z ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
  rw [sum_sub_distrib]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
  nlinarith

end KusnerL1
