import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! Scalar quantities in Sections 5–6 of the recorded manuscript. -/
namespace KusnerL1
open Real

noncomputable def h (w : ℝ) : ℝ := min 2 (3 - 2 * w)
noncomputable def a (R : ℝ) : ℝ := (R - 1) / (2 * (R + 1)) * log R
noncomputable def b (R : ℝ) : ℝ := R / (R + 1) ^ 2
noncomputable def alpha (M : ℝ) : ℝ :=
  if M = 2 then 1 / 4 else log ((M + 2) / 4) / (M - 2)
noncomputable def Phi (n : ℕ) (M w : ℝ) : ℝ := (2 * n * w + 2 / M) * h w
noncomputable def G (n : ℕ) (M z : ℝ) : ℝ :=
  log ((2 * n - 1) * z / 4) - (z - 2) * alpha M

def Admissible (n : ℕ) (M w : ℝ) : Prop :=
  2 ≤ M ∧ M ≤ 2 * ((n : ℝ) - 1) ∧ 2 / M ≤ w ∧ w ≤ 1

theorem log_twenty_lt : log (20 : ℝ) < 3 := by
  apply (log_lt_iff_lt_exp (by norm_num)).2
  have H := Real.sum_le_exp_of_nonneg (x := 3) (by norm_num) 10
  norm_num [Finset.sum_range_succ] at H
  linarith

theorem log_twenty_two_thirds_lt : log (22 / 3 : ℝ) < 2 := by
  apply (log_lt_iff_lt_exp (by norm_num)).2
  have H := Real.sum_le_exp_of_nonneg (x := 2) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at H
  linarith

theorem log_ninety_nine_tenths_lt : log (99 / 10 : ℝ) < 23 / 10 := by
  apply (log_lt_iff_lt_exp (by norm_num)).2
  have H := Real.sum_le_exp_of_nonneg (x := 23 / 10) (by norm_num) 9
  norm_num [Finset.sum_range_succ] at H
  linarith

theorem log_thirteen_eighths_gt : (10 / 21 : ℝ) < log (13 / 8 : ℝ) := by
  have H := Real.sum_range_le_log_div (x := 5 / 21) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at H
  linarith

theorem alpha_le_quarter {M : ℝ} (hM : 2 ≤ M) : alpha M ≤ 1 / 4 := by
  rcases eq_or_lt_of_le hM with rfl | hM
  · norm_num [alpha]
  · rw [alpha, if_neg (ne_of_gt hM), div_le_iff₀ (by linarith)]
    have H := log_le_sub_one_of_pos (x := (M + 2) / 4) (by positivity)
    linarith

theorem alpha_pos {M : ℝ} (hM : 2 ≤ M) : 0 < alpha M := by
  rcases eq_or_lt_of_le hM with rfl | hM
  · norm_num [alpha]
  · rw [alpha, if_neg (ne_of_gt hM)]
    exact div_pos (log_pos (by linarith)) (by linarith)

theorem alpha_antitone {M N : ℝ} (hM : 2 ≤ M) (hMN : M ≤ N) : alpha N ≤ alpha M := by
  rcases eq_or_lt_of_le hM with rfl | hM
  · simpa [alpha] using alpha_le_quarter hMN
  have hN : 2 < N := hM.trans_le hMN
  have H := strictConcaveOn_log_Ioi.concaveOn.antitoneOn_slope_gt
    (x := (4 : ℝ)) (by norm_num)
    (a := M + 2) (b := N + 2)
    ⟨by change 0 < M + 2; linarith, by linarith⟩ ⟨by change 0 < N + 2; linarith, by linarith⟩
    (by linarith)
  simpa [alpha, ne_of_gt hM, ne_of_gt hN, slope_def_field,
    log_div (by linarith : M + 2 ≠ 0) (by norm_num : (4 : ℝ) ≠ 0),
    log_div (by linarith : N + 2 ≠ 0) (by norm_num : (4 : ℝ) ≠ 0),
    show M + 2 - 4 = M - 2 by ring, show N + 2 - 4 = N - 2 by ring] using H

theorem logarithmic_chord {M u : ℝ} (hu : 2 ≤ u) (huM : u ≤ M) :
    log 4 + (u - 2) * alpha M ≤ log (u + 2) := by
  rcases eq_or_lt_of_le hu with rfl | hu
  · norm_num
  have H := mul_le_mul_of_nonneg_left (alpha_antitone hu.le huM) (by linarith : 0 ≤ u - 2)
  have E : (u - 2) * alpha u = log (u + 2) - log 4 := by
    rw [alpha, if_neg (ne_of_gt hu), mul_div_cancel₀ _ (by linarith),
      log_div (by linarith) (by norm_num)]
  rw [E] at H
  linarith

/-- A finite-difference form of the derivative comparison used in Section 6. -/
theorem G_mono_z {M x y : ℝ} (hM : 2 ≤ M) (hx : 0 < x)
    (hxy : x ≤ y) (hy : y ≤ 4) : G 6 M x ≤ G 6 M y := by
  have hyp : 0 < y := hx.trans_le hxy
  have H := log_le_sub_one_of_pos (x := x / y) (div_pos hx hyp)
  rw [log_div hx.ne' hyp.ne'] at H
  have H' : log x - log y ≤ (x - y) / y := by
    simpa [sub_div, div_self hyp.ne'] using H
  have H'' : (x - y) / y ≤ (x - y) / 4 := by
    apply (div_le_div_iff₀ hyp (by norm_num)).2
    nlinarith
  have ha := alpha_le_quarter hM
  have Hmul := mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hxy)
  have Ex : (11 : ℝ) * x / 4 = (11 / 4) * x := by ring
  have Ey : (11 : ℝ) * y / 4 = (11 / 4) * y := by ring
  simp only [G, Nat.cast_ofNat]
  norm_num
  rw [Ex, Ey, log_mul (by norm_num) hx.ne', log_mul (by norm_num) hyp.ne']
  linarith

theorem G_mono_M {M N z : ℝ} (hM : 2 ≤ M) (hMN : M ≤ N) (hz : 2 ≤ z) :
    G 6 M z ≤ G 6 N z := by
  unfold G
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left (alpha_antitone hM hMN)
    (sub_nonneg.mpr hz)) _

theorem G_diagonal {M : ℝ} (hM : 2 ≤ M) : G 6 M M = log (11 * M / (M + 2)) := by
  have hMp : 0 < M := by linarith
  rcases eq_or_lt_of_le hM with rfl | hM
  · norm_num [G, alpha]
  have H : (M - 2) * alpha M = log ((M + 2) / 4) := by
    rw [alpha, if_neg (ne_of_gt hM), mul_div_cancel₀ _ (by linarith)]
  simp only [G, Nat.cast_ofNat]
  norm_num
  rw [H, ← log_div (by positivity) (by positivity)]
  congr 1
  field_simp

/-- The square-completion bound of Proposition `prop:average-span`. -/
theorem Phi_envelope {n : ℕ} (hn : 0 < n) {M w : ℝ} (hM : 0 < M) (hw : 0 ≤ w) :
    Phi n M w ≤ (3 * n + 2 / M) ^ 2 / (4 * n) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have H : Phi n M w ≤ (2 * n * w + 2 / M) * (3 - 2 * w) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnr
  have E : (2 * n * w + 2 / M) * (3 - 2 * w) =
      (3 * n + 2 / M) ^ 2 / (4 * n) -
        4 * n * (w - (3 * n - 2 / M) / (4 * n)) ^ 2 := by field_simp; ring
  rw [E] at H
  nlinarith [sq_nonneg (w - (3 * n - 2 / M) / (4 * n))]

theorem span_threshold {q : ℝ} (hq : q ≤ 3969 / 280) : a 20 + b 20 * q < 2 := by
  have H := log_twenty_lt
  norm_num [a, b]
  linarith

/-- Proposition `prop:scalar-exclusion`, with the actual logarithmic functions. -/
theorem scalar_exclusion_six {M w : ℝ} (H : Admissible 6 M w) :
    a 20 + b 20 * Phi 6 M w < 2 ∨ 1 + (1 / 2) * G 6 M (M * w) < 2 := by
  rcases H with ⟨hM, hMu, hwl, hwu⟩
  have hMp : 0 < M := by linarith
  have hwp : 0 < w := (div_pos (by norm_num) hMp).trans_le hwl
  have hz : 2 ≤ M * w := by nlinarith [(div_le_iff₀ hMp).mp hwl]
  have hzM : M * w ≤ M := by nlinarith
  by_cases hc1 : M ≤ 4
  · right
    have H1 := G_mono_z hM (by positivity : 0 < M * w) hzM hc1
    rw [G_diagonal hM] at H1
    have H2 : 11 * M / (M + 2) ≤ (22 / 3 : ℝ) := by
      apply (div_le_iff₀ (by linarith)).2
      linarith
    have H3 := log_le_log (by positivity : 0 < 11 * M / (M + 2)) H2
    linarith [log_twenty_two_thirds_lt]
  by_cases hc4 : 9 / 2 ≤ M
  · left
    apply span_threshold
    have Hi : 2 / M ≤ (4 / 9 : ℝ) := by
      apply (div_le_iff₀ hMp).2
      linarith
    have He := Phi_envelope (n := 6) (by norm_num) hMp hwp.le
    norm_num at He
    have Hi0 : 0 ≤ 2 / M := by positivity
    nlinarith
  by_cases hc2 : w ≤ 4 / 5
  · right
    have hz18 : M * w ≤ 18 / 5 := by nlinarith
    have H1 := G_mono_M hM (by linarith : M ≤ 9 / 2) hz
    have H2 := G_mono_z (M := 9 / 2) (by norm_num)
      (by positivity : 0 < M * w) hz18 (by norm_num : (18 / 5 : ℝ) ≤ 4)
    have E : G 6 (9 / 2) (18 / 5) = log (99 / 10) - 16 / 25 * log (13 / 8) := by
      norm_num [G, alpha]
      ring
    rw [E] at H2
    linarith [log_ninety_nine_tenths_lt, log_thirteen_eighths_gt]
  · left
    apply span_threshold
    have Hi : 2 / M ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ hMp).2
      linarith
    have H1 : Phi 6 M w ≤ (12 * w + 2 / M) * (3 - 2 * w) := by
      simpa only [Phi, h, Nat.cast_ofNat, show (2 : ℝ) * 6 = 12 by norm_num] using mul_le_mul_of_nonneg_left (min_le_right (2 : ℝ) (3 - 2 * w))
        (by positivity : 0 ≤ 12 * w + 2 / M)
    have H2 : (12 * w + 2 / M) * (3 - 2 * w) ≤ (12 * w + 1 / 2) * (3 - 2 * w) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have H3 : (12 * w + 1 / 2) * (3 - 2 * w) ≤ (707 / 50 : ℝ) := by
      nlinarith [sq_nonneg (w - 4 / 5)]
    linarith

/-- The necessary inequalities as stated in Corollary `cor:scalar-obstruction`. -/
def ScalarConditions (n : ℕ) (M w : ℝ) : Prop :=
  Admissible n M w ∧ (∀ R : ℝ, 1 < R → 2 ≤ a R + b R * Phi n M w) ∧
    2 ≤ 1 + (1 / 2) * G n M (M * w)

theorem admissible_mono {n N : ℕ} (hnN : n ≤ N) {M w : ℝ}
    (H : Admissible n M w) : Admissible N M w := by
  have hcast : (n : ℝ) ≤ N := by exact_mod_cast hnN
  rcases H with ⟨h1, h2, h3, h4⟩
  exact ⟨h1, by linarith, h3, h4⟩

theorem Phi_dimension_mono {n N : ℕ} (hnN : n ≤ N) {M w : ℝ}
    (hw : 0 ≤ w) (hw1 : w ≤ 1) : Phi n M w ≤ Phi N M w := by
  have hcast : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hh : 0 ≤ h w := le_min (by norm_num) (by linarith)
  exact mul_le_mul_of_nonneg_right (by nlinarith) hh

theorem G_dimension_mono {n N : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N) {M z : ℝ}
    (hz : 0 < z) : G n M z ≤ G N M z := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hcast : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hp : 0 < 2 * (n : ℝ) - 1 := by linarith
  unfold G
  apply sub_le_sub_right
  apply log_le_log
  · positivity
  · nlinarith

/-- The first exact difference in Lemma `lem:dimension-monotonicity`. -/
theorem Phi_dimension_step (n : ℕ) (M w : ℝ) :
    Phi (n + 1) M w - Phi n M w = 2 * w * h w := by
  unfold Phi
  push_cast
  ring

/-- The second exact difference in Lemma `lem:dimension-monotonicity`. -/
theorem G_dimension_step {n : ℕ} (hn : 2 ≤ n) (M : ℝ) {z : ℝ} (hz : 0 < z) :
    G (n + 1) M z - G n M z = log ((2 * n + 1 : ℝ) / (2 * n - 1)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < 2 * (n : ℝ) - 1 := by linarith
  have hq : 0 < 2 * (n : ℝ) + 1 := by positivity
  unfold G
  push_cast
  rw [show (2 : ℝ) * (n + 1) - 1 = 2 * n + 1 by ring]
  rw [log_div (mul_pos hq hz).ne' (by norm_num : (4 : ℝ) ≠ 0),
    log_div (mul_pos hp hz).ne' (by norm_num : (4 : ℝ) ≠ 0),
    log_mul hq.ne' hz.ne', log_mul hp.ne' hz.ne', log_div hq.ne' hp.ne']
  ring

/-- Both energy estimates strictly weaken when the dimension increases by one. -/
theorem dimension_bounds_strict {n : ℕ} (hn : 2 ≤ n) {M w R : ℝ}
    (H : Admissible n M w) (hR : 1 < R) :
    a R + b R * Phi n M w < a R + b R * Phi (n + 1) M w ∧
      1 + 1 / 2 * G n M (M * w) < 1 + 1 / 2 * G (n + 1) M (M * w) := by
  have hM : 0 < M := by linarith [H.1]
  have hw : 0 < w := (div_pos (by norm_num) hM).trans_le H.2.2.1
  have hh : 0 < h w := lt_min (by norm_num) (by linarith [H.2.2.2])
  have hb : 0 < b R := by unfold b; positivity
  have hP := Phi_dimension_step n M w
  have hPd : 0 < 2 * w * h w := by positivity
  have hG := G_dimension_step hn M (mul_pos hM hw)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hGd : 0 < log ((2 * n + 1 : ℝ) / (2 * n - 1)) := by
    apply log_pos
    exact (one_lt_div (by linarith)).mpr (by linarith)
  constructor
  · nlinarith [mul_pos hb hPd]
  · linarith

/-- Corollary `cor:downward-exclusion`, expressed as upward propagation of a
hypothetical solution to the necessary scalar inequalities. -/
theorem scalarConditions_mono {n N : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N)
    {M w : ℝ} (H : ScalarConditions n M w) : ScalarConditions N M w := by
  rcases H with ⟨ha, hs, he⟩
  have hMp : 0 < M := by linarith [ha.1]
  have hwp : 0 < w := (div_pos (by norm_num) hMp).trans_le ha.2.2.1
  refine ⟨admissible_mono hnN ha, ?_, ?_⟩
  · intro R hR
    have hb : 0 ≤ b R := by unfold b; positivity
    have hp := mul_le_mul_of_nonneg_left (Phi_dimension_mono hnN (M := M) hwp.le ha.2.2.2) hb
    linarith [hs R hR]
  · have H := G_dimension_mono hn hnN (M := M) (mul_pos hMp hwp)
    linarith

theorem no_scalar_solution {n : ℕ} (hn : 2 ≤ n) (hn6 : n ≤ 6) (M w : ℝ) :
    ¬ ScalarConditions n M w := by
  intro H
  obtain ⟨ha, hs, he⟩ := scalarConditions_mono hn hn6 H
  rcases scalar_exclusion_six ha with h | h
  · exact (not_lt_of_ge (hs 20 (by norm_num))) h
  · exact (not_lt_of_ge he) h

end KusnerL1
