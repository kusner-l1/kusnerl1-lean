import KusnerL1.TestFunctions
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The endpoint-sensitive test function of Proposition `prop:endpoint-bound`.
The central interval is denoted `[A,C]`, with `C = T-B` in the manuscript. -/
namespace KusnerL1
open Real Set

noncomputable def q (T t : ℝ) : ℝ := t * (T - t) / T

lemma q_pos {T t : ℝ} (hT : 0 < T) (ht : 0 < t) (htT : t < T) : 0 < q T t := by
  exact div_pos (mul_pos ht (sub_pos.mpr htT)) hT

lemma hasDerivAt_q (T t : ℝ) : HasDerivAt (q T) ((T - 2 * t) / T) t := by
  have H := ((hasDerivAt_id t).mul ((hasDerivAt_const t T).sub (hasDerivAt_id t))).div_const T
  apply H.congr_deriv
  dsimp
  ring

noncomputable def sqrtQDeriv (T t : ℝ) : ℝ := ((T - 2 * t) / T) / (2 * sqrt (q T t))
noncomputable def endpointPrimitive (T t : ℝ) : ℝ := (1 / 4) * (log t - log (T - t)) - t / T

lemma hasDerivAt_sqrtQ {T t : ℝ} (hT : 0 < T) (ht : 0 < t) (htT : t < T) :
    HasDerivAt (fun t => sqrt (q T t)) (sqrtQDeriv T t) t :=
  (hasDerivAt_q T t).sqrt (q_pos hT ht htT).ne'

lemma sqrtQDeriv_sq {T t : ℝ} (hT : 0 < T) (ht : 0 < t) (htT : t < T) :
    sqrtQDeriv T t ^ 2 = 1 / (4 * t) + 1 / (4 * (T - t)) - 1 / T := by
  unfold sqrtQDeriv
  rw [div_pow, mul_pow, Real.sq_sqrt (q_pos hT ht htT).le]
  unfold q
  field_simp [hT.ne', ht.ne', show T - t ≠ 0 by linarith]
  ring

lemma hasDerivAt_endpointPrimitive {T t : ℝ} (hT : 0 < T) (ht : 0 < t) (htT : t < T) :
    HasDerivAt (endpointPrimitive T) (sqrtQDeriv T t ^ 2) t := by
  rw [sqrtQDeriv_sq hT ht htT]
  have H := (((Real.hasDerivAt_log ht.ne').sub
    (((hasDerivAt_const t T).sub (hasDerivAt_id t)).log (by change T - t ≠ 0; linarith))).const_mul (1 / 4)).sub
      ((hasDerivAt_id t).div_const T)
  apply H.congr_deriv
  dsimp
  field_simp [hT.ne', ht.ne', show T - t ≠ 0 by linarith]
  ring

lemma continuousOn_sqrtQDeriv {T A C : ℝ} (hT : 0 < T) (hA : 0 < A) (hC : C < T) :
    ContinuousOn (sqrtQDeriv T) (Icc A C) := by
  unfold sqrtQDeriv q
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro t ht
    apply mul_ne_zero (by norm_num)
    apply Real.sqrt_ne_zero'.mpr
    exact q_pos hT (hA.trans_le ht.1) (ht.2.trans_lt hC)

/-- The central Dirichlet integral is the difference of the logarithmic primitive. -/
lemma endpoint_central_secant {T A C : ℝ} (hT : 0 < T) (hA : 0 < A) (hC : C < T) :
    SecantBound (fun t => sqrt (q T t)) (endpointPrimitive T) A C := by
  apply secant_of_deriv (D := sqrtQDeriv T)
  · intro t ht
    exact hasDerivAt_sqrtQ hT (hA.trans_le ht.1) (ht.2.trans_lt hC)
  · intro t ht
    exact hasDerivAt_endpointPrimitive hT (hA.trans_le ht.1) (ht.2.trans_lt hC)
  · exact continuousOn_sqrtQDeriv hT hA hC

/-- The prescribed endpoint test and its exact total Dirichlet energy.
The degenerate central interval `A = C` is included. -/
theorem endpoint_test {T A C : ℝ} (hT : 0 < T) (hA : 0 < A) (hAC : A ≤ C) (hC : C < T) :
    ∃ F E : ℝ → ℝ, F 0 = 0 ∧ F T = 0 ∧ SecantBound F E 0 T ∧
      (∀ t ∈ Icc A C, F t ^ 2 = q T t) ∧
      E T - E 0 = 1 + (1 / 4) * log ((T - A) * C / (A * (T - C))) := by
  let s := sqrt (q T A) / A
  let u := sqrt (q T C) / (T - C)
  let f₁ := fun t => s * t + 0
  let f₂ := fun t => sqrt (q T t)
  let f₃ := fun t => u * (T - t)
  let e₁ := fun t => s ^ 2 * t + 0
  let e₂ := fun t => e₁ A + endpointPrimitive T t - endpointPrimitive T A
  let e₃ := fun t => e₂ C + u ^ 2 * (t - C)
  have hFA : f₁ A = f₂ A := by dsimp [f₁, f₂, s]; field_simp; ring
  have hEA : e₁ A = e₂ A := by dsimp [e₂]; ring
  have hFC : f₂ C = f₃ C := by dsimp [f₂, f₃, u]; field_simp [show T - C ≠ 0 by linarith]
  have hEC : e₂ C = e₃ C := by dsimp [e₃]; ring
  have hs₁ : SecantBound f₁ e₁ 0 A := secant_affine s 0 0 0 A
  have hs₂ : SecantBound f₂ e₂ A C := by
    intro x hx y hy hxy
    have H := endpoint_central_secant hT hA hC x hx y hy hxy
    dsimp [f₂, e₂]
    linarith
  have hs₃ : SecantBound f₃ e₃ C T := by
    apply (secant_affine (-u) (u * T) (e₂ C - u ^ 2 * C) C T).congr
    · intro t ht; dsimp [f₃]; ring
    · intro t ht; dsimp [e₃]; ring
  let F := join C (join A f₁ f₂) f₃
  let E := join C (join A e₁ e₂) e₃
  have hFCC : join A f₁ f₂ C = f₃ C :=
    (join_right f₁ f₂ hFA ⟨hAC, le_rfl⟩).trans hFC
  have hECC : join A e₁ e₂ C = e₃ C :=
    (join_right e₁ e₂ hEA ⟨hAC, le_rfl⟩).trans hEC
  refine ⟨F, E, ?_, ?_, ?_, ?_, ?_⟩
  · simp [F, join, show 0 ≤ C by linarith, hA.le, f₁]
  · simp [F, join, not_le.mpr hC, f₃]
  · exact secant_join (by linarith) hC.le (secant_join hA.le hAC hs₁ hs₂ hFA hEA) hs₃ hFCC hECC
  · intro t ht
    have heq : F t = f₂ t := by
      dsimp [F]
      rw [join, if_pos ht.2]
      exact join_right f₁ f₂ hFA ht
    rw [heq]
    exact Real.sq_sqrt (q_pos hT (hA.trans_le ht.1) (ht.2.trans_lt hC)).le
  · have hTA : 0 < T - A := by linarith
    have hTC : 0 < T - C := by linarith
    have hCp : 0 < C := hA.trans_le hAC
    have hsqA := Real.sq_sqrt (q_pos hT hA (by linarith)).le
    have hsqC := Real.sq_sqrt (q_pos hT hCp hC).le
    simp only [E, join, if_neg (not_le.mpr hC), if_pos (show 0 ≤ C by linarith), if_pos hA.le,
      e₃, e₂, e₁, add_zero, mul_zero, sub_zero]
    rw [log_div (mul_ne_zero hTA.ne' hCp.ne') (mul_ne_zero hA.ne' hTC.ne'),
      log_mul hTA.ne' hCp.ne', log_mul hA.ne' hTC.ne']
    dsimp [s, u, endpointPrimitive]
    rw [div_pow, div_pow, hsqA, hsqC]
    unfold q
    field_simp
    ring

end KusnerL1
