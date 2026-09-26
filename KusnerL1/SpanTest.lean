import KusnerL1.EndpointTest
import KusnerL1.Scalar

/-! The span-sensitive test function of Proposition `prop:span-bound`. -/
namespace KusnerL1
open Real Set

noncomputable def spanLambda (T d : ℝ) : ℝ := T * (1 - d ^ 2) / 4
noncomputable def spanLeft (T d : ℝ) : ℝ := T * (1 - d) / 2
noncomputable def spanRight (T d : ℝ) : ℝ := T * (1 + d) / 2
noncomputable def spanPrimitive (T d t : ℝ) : ℝ :=
  (d / 4) * (log (t - spanLeft T d) - log (spanRight T d - t)) - t / T
noncomputable def spanDeriv (T d t : ℝ) : ℝ :=
  ((T - 2 * t) / T) / (2 * sqrt (q T t - spanLambda T d))

lemma span_parameters {T d : ℝ} (hT : 0 < T) (hd : 0 < d) (hd1 : d < 1) :
    0 < spanLambda T d ∧ 2 * spanLambda T d < T - 2 * spanLambda T d ∧
      spanLeft T d < 2 * spanLambda T d ∧ T - 2 * spanLambda T d < spanRight T d := by
  have hs : 0 < 1 - d ^ 2 := by nlinarith
  have hp := mul_pos (mul_pos hT hd) (sub_pos.mpr hd1)
  have hq := mul_pos hT (sq_pos_of_pos hd)
  dsimp [spanLambda, spanLeft, spanRight]
  constructor
  · positivity
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma span_factor {T d t : ℝ} (hT : 0 < T) :
    q T t - spanLambda T d = (t - spanLeft T d) * (spanRight T d - t) / T := by
  unfold q spanLambda spanLeft spanRight
  field_simp
  ring

lemma span_rad_pos {T d t : ℝ} (hT : 0 < T) (htl : spanLeft T d < t)
    (htr : t < spanRight T d) : 0 < q T t - spanLambda T d := by
  rw [span_factor hT]
  exact div_pos (mul_pos (sub_pos.mpr htl) (sub_pos.mpr htr)) hT

lemma hasDerivAt_spanSqrt {T d t : ℝ} (hT : 0 < T) (htl : spanLeft T d < t)
    (htr : t < spanRight T d) :
    HasDerivAt (fun t => sqrt (q T t - spanLambda T d)) (spanDeriv T d t) t :=
  ((hasDerivAt_q T t).sub_const (spanLambda T d)).sqrt (span_rad_pos hT htl htr).ne'

lemma spanDeriv_sq {T d t : ℝ} (hT : 0 < T) (htl : spanLeft T d < t)
    (htr : t < spanRight T d) :
    spanDeriv T d t ^ 2 = (d / 4) * (1 / (t - spanLeft T d) + 1 / (spanRight T d - t)) - 1 / T := by
  unfold spanDeriv
  rw [div_pow, mul_pow, Real.sq_sqrt (span_rad_pos hT htl htr).le, span_factor hT]
  have h₁ : t - spanLeft T d ≠ 0 := sub_ne_zero.mpr (ne_of_gt htl)
  have h₂ : spanRight T d - t ≠ 0 := sub_ne_zero.mpr (ne_of_gt htr)
  field_simp [hT.ne', h₁, h₂]
  unfold spanLeft spanRight
  ring

lemma hasDerivAt_spanPrimitive {T d t : ℝ} (hT : 0 < T) (htl : spanLeft T d < t)
    (htr : t < spanRight T d) :
    HasDerivAt (spanPrimitive T d) (spanDeriv T d t ^ 2) t := by
  rw [spanDeriv_sq hT htl htr]
  have H := ((((hasDerivAt_id t).sub_const (spanLeft T d)).log (by dsimp; linarith)).sub
    (((hasDerivAt_const t (spanRight T d)).sub (hasDerivAt_id t)).log (by dsimp; linarith))).const_mul (d / 4)
  apply (H.sub ((hasDerivAt_id t).div_const T)).congr_deriv
  dsimp
  ring

lemma span_central_secant {T d : ℝ} (hT : 0 < T) (hd : 0 < d) (hd1 : d < 1) :
    SecantBound (fun t => sqrt (q T t - spanLambda T d)) (spanPrimitive T d)
      (2 * spanLambda T d) (T - 2 * spanLambda T d) := by
  obtain ⟨hlam, hmid, hl, hr⟩ := span_parameters hT hd hd1
  apply secant_of_deriv (D := spanDeriv T d)
  · intro t ht
    exact hasDerivAt_spanSqrt hT (hl.trans_le ht.1) (ht.2.trans_lt hr)
  · intro t ht
    exact hasDerivAt_spanPrimitive hT (hl.trans_le ht.1) (ht.2.trans_lt hr)
  · unfold spanDeriv q
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro t ht
      exact mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr
        (span_rad_pos hT (hl.trans_le ht.1) (ht.2.trans_lt hr)))

lemma span_junction_square {T d : ℝ} (hT : 0 < T) :
    q T (2 * spanLambda T d) - spanLambda T d = spanLambda T d * d ^ 2 := by
  unfold q spanLambda
  field_simp
  ring

lemma q_reflect (T t : ℝ) : q T (T - t) = q T t := by unfold q; ring

lemma span_primitive_difference {T d : ℝ} (hT : 0 < T) (hd : 0 < d) (hd1 : d < 1) :
    spanPrimitive T d (T - 2 * spanLambda T d) - spanPrimitive T d (2 * spanLambda T d) =
      d / 2 * log ((1 + d) / (1 - d)) - d ^ 2 := by
  let K := T * d / 2
  have hK : 0 < K := by dsimp [K]; positivity
  have h₁ : 2 * spanLambda T d - spanLeft T d = K * (1 - d) := by
    dsimp [spanLambda, spanLeft, K]; ring
  have h₂ : spanRight T d - 2 * spanLambda T d = K * (1 + d) := by
    dsimp [spanLambda, spanRight, K]; ring
  have h₃ : (T - 2 * spanLambda T d) - spanLeft T d = K * (1 + d) := by
    dsimp [spanLambda, spanLeft, K]; ring
  have h₄ : spanRight T d - (T - 2 * spanLambda T d) = K * (1 - d) := by
    dsimp [spanLambda, spanRight, K]; ring
  unfold spanPrimitive
  rw [h₁, h₂, h₃, h₄, log_mul hK.ne' (by linarith : 1 - d ≠ 0),
    log_mul hK.ne' (by linarith : 1 + d ≠ 0), log_div (by linarith : 1 + d ≠ 0) (by linarith : 1 - d ≠ 0)]
  unfold spanLambda
  field_simp
  ring

lemma span_terminal_error {T d t : ℝ} (hT : 0 < T) (hlam : 0 < spanLambda T d) :
    (d / (2 * sqrt (spanLambda T d)) * t) ^ 2 + spanLambda T d - q T t =
      (t - 2 * spanLambda T d) ^ 2 / (4 * spanLambda T d) := by
  rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hlam.le]
  unfold q
  field_simp [hT.ne', hlam.ne']
  unfold spanLambda
  ring

/-- The prescribed span test and its total Dirichlet energy, parametrized by
`d = (R-1)/(R+1)` as in the proof. -/
theorem span_test {T d : ℝ} (hT : 0 < T) (hd : 0 < d) (hd1 : d < 1) :
    ∃ F E : ℝ → ℝ, F 0 = 0 ∧ F T = 0 ∧ SecantBound F E 0 T ∧
      (∀ t ∈ Icc 0 T, q T t ≤ F t ^ 2 + spanLambda T d) ∧
      E T - E 0 = d / 2 * log ((1 + d) / (1 - d)) := by
  obtain ⟨hlam, hmid, hl, hr⟩ := span_parameters hT hd hd1
  let τ := 2 * spanLambda T d
  let C := T - τ
  let s := d / (2 * sqrt (spanLambda T d))
  let f₁ := fun t => s * t + 0
  let f₂ := fun t => sqrt (q T t - spanLambda T d)
  let f₃ := fun t => s * (T - t)
  let e₁ := fun t => s ^ 2 * t + 0
  let e₂ := fun t => e₁ τ + spanPrimitive T d t - spanPrimitive T d τ
  let e₃ := fun t => e₂ C + s ^ 2 * (t - C)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hC : C < T := by dsimp [C]; linarith
  have hτC : τ ≤ C := hmid.le
  have hsqrt : sqrt (q T τ - spanLambda T d) = d * sqrt (spanLambda T d) := by
    rw [span_junction_square hT, Real.sqrt_mul hlam.le, Real.sqrt_sq_eq_abs, abs_of_pos hd, mul_comm]
  have hFA : f₁ τ = f₂ τ := by
    dsimp [f₁, f₂]
    rw [hsqrt]
    dsimp [s, τ]
    have hsq := Real.sq_sqrt hlam.le
    field_simp [Real.sqrt_ne_zero'.mpr hlam]
    nlinarith
  have hFC : f₂ C = f₃ C := by
    dsimp [f₂, f₃, C]
    rw [q_reflect, hsqrt]
    dsimp [s, τ]
    have hsq := Real.sq_sqrt hlam.le
    field_simp [Real.sqrt_ne_zero'.mpr hlam]
    nlinarith
  have hEA : e₁ τ = e₂ τ := by dsimp [e₂]; ring
  have hEC : e₂ C = e₃ C := by dsimp [e₃]; ring
  have hs₁ : SecantBound f₁ e₁ 0 τ := secant_affine s 0 0 0 τ
  have hs₂ : SecantBound f₂ e₂ τ C := by
    intro x hx y hy hxy
    have H := span_central_secant hT hd hd1 x hx y hy hxy
    dsimp [f₂, e₂]
    linarith
  have hs₃ : SecantBound f₃ e₃ C T := by
    apply (secant_affine (-s) (s * T) (e₂ C - s ^ 2 * C) C T).congr
    · intro t ht; dsimp [f₃]; ring
    · intro t ht; dsimp [e₃]; ring
  let F := join C (join τ f₁ f₂) f₃
  let E := join C (join τ e₁ e₂) e₃
  have hFCC : join τ f₁ f₂ C = f₃ C := (join_right f₁ f₂ hFA ⟨hτC, le_rfl⟩).trans hFC
  have hECC : join τ e₁ e₂ C = e₃ C := (join_right e₁ e₂ hEA ⟨hτC, le_rfl⟩).trans hEC
  refine ⟨F, E, ?_, ?_, ?_, ?_, ?_⟩
  · simp [F, join, show 0 ≤ C by linarith, hτ.le, f₁]
  · simp [F, join, not_le.mpr hC, f₃]
  · exact secant_join (by linarith) hC.le (secant_join hτ.le hτC hs₁ hs₂ hFA hEA) hs₃ hFCC hECC
  · intro t ht
    by_cases htC : t ≤ C
    · by_cases htτ : t ≤ τ
      · have He := span_terminal_error (t := t) hT hlam
        have Hp := div_nonneg (sq_nonneg (t - 2 * spanLambda T d)) (by positivity : 0 ≤ 4 * spanLambda T d)
        simp only [F, join, if_pos htC, if_pos htτ, f₁, add_zero, s]
        linarith
      · simp only [F, join, if_pos htC, if_neg htτ, f₂]
        rw [Real.sq_sqrt (span_rad_pos hT (by linarith) (by linarith)).le]
        linarith
    · have He := span_terminal_error (t := T - t) hT hlam
      have Hp := div_nonneg (sq_nonneg (T - t - 2 * spanLambda T d)) (by positivity : 0 ≤ 4 * spanLambda T d)
      rw [q_reflect] at He
      simp only [F, join, if_neg htC, f₃, s]
      linarith
  · simp only [E, join, if_neg (not_le.mpr hC), if_pos (show 0 ≤ C by linarith), if_pos hτ.le,
      e₃, e₂, e₁, add_zero, mul_zero, sub_zero]
    have HP := span_primitive_difference hT hd hd1
    change spanPrimitive T d C - spanPrimitive T d τ = _ at HP
    have Hs : 2 * s ^ 2 * τ = d ^ 2 := by
      dsimp [s, τ]
      rw [div_pow, mul_pow, Real.sq_sqrt hlam.le]
      field_simp
    dsimp [C]
    linarith

end KusnerL1
