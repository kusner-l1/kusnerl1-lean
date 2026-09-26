import KusnerL1.CoordinateTest
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The Cauchy–Schwarz step underlying the Dirichlet estimate. -/
namespace KusnerL1
open MeasureTheory intervalIntegral Set

/-- The squared integral is bounded by interval length times quadratic energy.
The proof integrates the square of the deviation from the interval mean. -/
theorem integral_square_bound {a b : ℝ} (hab : a < b) (D : ℝ → ℝ)
    (hD : IntervalIntegrable D volume a b)
    (hD2 : IntervalIntegrable (fun t => D t ^ 2) volume a b) :
    (∫ t in a..b, D t) ^ 2 / (b - a) ≤ ∫ t in a..b, D t ^ 2 := by
  let c : ℝ := (∫ t in a..b, D t) / (b - a)
  have H := integral_nonneg_of_forall (μ := volume) hab.le (fun t => sq_nonneg (D t - c))
  have He : (fun t => (D t - c) ^ 2) = (fun t => D t ^ 2 - (2 * c) * D t + c ^ 2) := by
    funext t
    ring
  rw [He, integral_add (hD2.sub (hD.const_mul (2 * c))) intervalIntegrable_const,
    integral_sub hD2 (hD.const_mul (2 * c)), intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at H
  simp only [smul_eq_mul] at H
  have hba : 0 < b - a := by linarith
  apply (div_le_iff₀ hba).2
  have hc : c * (b - a) = ∫ t in a..b, D t := div_mul_cancel₀ _ hba.ne'
  nlinarith [mul_nonneg hba.le H]

/-- The fundamental-theorem-of-calculus form of the one-interval test estimate.
One-sided derivatives allow junctions of piecewise differentiable functions. -/
theorem dirichlet_secant_bound {a b : ℝ} (hab : a < b) (F D : ℝ → ℝ)
    (hF : ContinuousOn F (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivWithinAt F (D t) (Ioi t) t)
    (hD : IntervalIntegrable D volume a b)
    (hD2 : IntervalIntegrable (fun t => D t ^ 2) volume a b) :
    (F b - F a) ^ 2 / (b - a) ≤ ∫ t in a..b, D t ^ 2 := by
  rw [← integral_eq_sub_of_hasDeriv_right_of_le hab.le hF hderiv hD]
  exact integral_square_bound hab D hD hD2

/-- The integral estimate in Lemma `lem:coordinate-test`, with continuity,
one-sided derivatives and integrability made explicit. The two concrete test
functions in Section 4 still require their own analytic verification. -/
theorem coordinate_test_integral {m n : ℕ} (hm : 0 < m) (y : Fin m → L1 n) (r : Fin m → ℝ)
    (hr : ∀ i, 0 < r i) (hs : Star y r) (j : Fin n) (F D : ℝ → ℝ)
    (hF0 : F 0 = 0) (hFT : F (totalMass r) = 0)
    (hF : ContinuousOn F (Icc 0 (totalMass r)))
    (hderiv : ∀ t ∈ Ioo 0 (totalMass r), HasDerivWithinAt F (D t) (Ioi t) t)
    (hD : IntervalIntegrable D volume 0 (totalMass r))
    (hD2 : IntervalIntegrable (fun t => D t ^ 2) volume 0 (totalMass r)) :
    (∑ k : Fin m, gap hm (fun i => y i j) k *
      F (cumulative (fun i => y i j) (mass r) (k.val + 1)) ^ 2) ≤
        ∫ t in 0..totalMass r, D t ^ 2 := by
  let v := fun i => y i j
  let t := cumulative v (mass r)
  have hμ : ∀ i, 0 < mass r i := fun i => inv_pos.mpr (hr i)
  have ht (k : ℕ) : 0 ≤ t k ∧ t k ≤ totalMass r := cumulative_bounds v (mass r) (fun i => (hμ i).le) k
  have hstep (k : Fin m) : t k.val < t (k.val + 1) := by
    have H := cumulative_succ v (mass r) k
    have := hμ (order v k)
    dsimp [t]
    linarith
  have hsub (k : Fin m) : uIcc (t k.val) (t (k.val + 1)) ⊆ uIcc 0 (totalMass r) := by
    rw [uIcc_of_le (hstep k).le, uIcc_of_le (le_trans (ht 0).1 (ht 0).2)]
    exact Icc_subset_Icc (ht _).1 (ht _).2
  calc
    _ ≤ ∑ k : Fin m, (F (t (k.val + 1)) - F (t k.val)) ^ 2 / (t (k.val + 1) - t k.val) :=
      coordinate_test_discrete hm y r hr hs j F hF0 hFT
    _ ≤ ∑ k : Fin m, ∫ u in t k.val..t (k.val + 1), D u ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      apply dirichlet_secant_bound (hstep k) F D
      · exact hF.mono (Icc_subset_Icc (ht _).1 (ht _).2)
      · intro u hu
        exact hderiv u ⟨lt_of_le_of_lt (ht _).1 hu.1, lt_of_lt_of_le hu.2 (ht _).2⟩
      · exact hD.mono_set (hsub k)
      · exact hD2.mono_set (hsub k)
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range (fun k => ∫ u in t k..t (k + 1), D u ^ 2) m,
        sum_integral_adjacent_intervals (fun k hk => hD2.mono_set (hsub ⟨k, hk⟩))]
      simp only [t, cumulative_zero, cumulative_end, totalMass]

end KusnerL1
