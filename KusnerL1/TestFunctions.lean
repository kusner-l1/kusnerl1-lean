import KusnerL1.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Branchwise Dirichlet estimates for the manuscript's two test functions.
Energy primitives record the integrals of squared derivatives. Joining at a
junction uses the same Cauchy–Schwarz inequality on the two subintervals. -/
namespace KusnerL1
open Set MeasureTheory intervalIntegral
open scoped BigOperators

/-- The integral test estimate, with the integral expressed by its primitive. -/
def SecantBound (F E : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x < y →
    (F y - F x) ^ 2 / (y - x) ≤ E y - E x

theorem square_div_add (x y a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (x + y) ^ 2 / (a + b) ≤ x ^ 2 / a + y ^ 2 / b := by
  apply (div_le_iff₀ (add_pos ha hb)).2
  have H : (x ^ 2 / a + y ^ 2 / b) * (a + b) - (x + y) ^ 2 =
      (b * x - a * y) ^ 2 / (a * b) := by field_simp; ring
  have hp := div_nonneg (sq_nonneg (b * x - a * y)) (mul_pos ha hb).le
  linarith

theorem SecantBound.glue {F E : ℝ → ℝ} {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hl : SecantBound F E a c) (hr : SecantBound F E c b) : SecantBound F E a b := by
  intro x hx y hy hxy
  by_cases hyc : y ≤ c
  · exact hl x ⟨hx.1, hxy.le.trans hyc⟩ y ⟨hy.1, hyc⟩ hxy
  by_cases hcx : c ≤ x
  · exact hr x ⟨hcx, hx.2⟩ y ⟨hcx.trans hxy.le, hy.2⟩ hxy
  have hxc : x < c := lt_of_not_ge hcx
  have hcy : c < y := lt_of_not_ge hyc
  have Hl := hl x ⟨hx.1, hxc.le⟩ c ⟨hac, le_rfl⟩ hxc
  have Hr := hr c ⟨le_rfl, hcb⟩ y ⟨hcy.le, hy.2⟩ hcy
  have H := square_div_add (F c - F x) (F y - F c) (c - x) (y - c)
    (by linarith) (by linarith)
  have hf : F c - F x + (F y - F c) = F y - F x := by ring
  have he : c - x + (y - c) = y - x := by ring
  rw [hf, he] at H
  linarith

noncomputable def join (c : ℝ) (f g : ℝ → ℝ) (t : ℝ) : ℝ := if t ≤ c then f t else g t

theorem join_left {a c : ℝ} (f g : ℝ → ℝ) : EqOn (join c f g) f (Icc a c) := by
  intro x hx
  exact if_pos hx.2

theorem join_right {c b : ℝ} (f g : ℝ → ℝ) (he : f c = g c) :
    EqOn (join c f g) g (Icc c b) := by
  intro x hx
  by_cases h : x ≤ c
  · have : x = c := le_antisymm h hx.1
    subst x
    simpa [join] using he
  · exact if_neg h

theorem SecantBound.congr {F E F' E' : ℝ → ℝ} {a b : ℝ}
    (h : SecantBound F E a b) (hf : EqOn F' F (Icc a b)) (he : EqOn E' E (Icc a b)) :
    SecantBound F' E' a b := by
  intro x hx y hy hxy
  rw [hf hx, hf hy, he hx, he hy]
  exact h x hx y hy hxy

theorem secant_join {F₁ F₂ E₁ E₂ : ℝ → ℝ} {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hl : SecantBound F₁ E₁ a c) (hr : SecantBound F₂ E₂ c b)
    (hF : F₁ c = F₂ c) (hE : E₁ c = E₂ c) :
    SecantBound (join c F₁ F₂) (join c E₁ E₂) a b :=
  (hl.congr (join_left _ _) (join_left _ _)).glue hac hcb
    (hr.congr (join_right _ _ hF) (join_right _ _ hE))

theorem secant_of_deriv {F D E : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ t ∈ Icc a b, HasDerivAt F (D t) t)
    (hE : ∀ t ∈ Icc a b, HasDerivAt E (D t ^ 2) t)
    (hD : ContinuousOn D (Icc a b)) : SecantBound F E a b := by
  intro x hx y hy hxy
  have hsub : uIcc x y ⊆ Icc a b := by
    rw [uIcc_of_le hxy.le]
    exact Icc_subset_Icc hx.1 hy.2
  have hi : IntervalIntegrable D volume x y := (hD.mono hsub).intervalIntegrable
  have hi2 : IntervalIntegrable (fun t => D t ^ 2) volume x y := ((hD.pow 2).mono hsub).intervalIntegrable
  have H := integral_square_bound hxy D hi hi2
  rw [integral_eq_sub_of_hasDerivAt (fun t ht => hF t (hsub ht)) hi,
    integral_eq_sub_of_hasDerivAt (fun t ht => hE t (hsub ht)) hi2] at H
  exact H

theorem secant_affine (s u v a b : ℝ) :
    SecantBound (fun t => s * t + u) (fun t => s ^ 2 * t + v) a b := by
  intro x hx y hy hxy
  have hne : y - x ≠ 0 := by linarith
  apply le_of_eq
  field_simp
  ring

/-- Summing the interval estimates gives exactly the integral test argument,
with the total Dirichlet energy written as `E T - E 0`. -/
theorem coordinate_test_secant {m n : ℕ} (hm : 0 < m) (y : Fin m → L1 n) (r : Fin m → ℝ)
    (hr : ∀ i, 0 < r i) (hs : Star y r) (j : Fin n) (F E : ℝ → ℝ)
    (hF0 : F 0 = 0) (hFT : F (totalMass r) = 0)
    (hFE : SecantBound F E 0 (totalMass r)) :
    (∑ k : Fin m, gap hm (fun i => y i j) k *
      F (cumulative (fun i => y i j) (mass r) (k.val + 1)) ^ 2) ≤ E (totalMass r) - E 0 := by
  let v := fun i => y i j
  let t := cumulative v (mass r)
  have hμ : ∀ i, 0 < mass r i := fun i => inv_pos.mpr (hr i)
  have ht (k : ℕ) : t k ∈ Icc 0 (totalMass r) := cumulative_bounds v (mass r) (fun i => (hμ i).le) k
  have hstep (k : Fin m) : t k.val < t (k.val + 1) := by
    have H := cumulative_succ v (mass r) k
    have := hμ (order v k)
    dsimp [t]
    linarith
  calc
    _ ≤ ∑ k : Fin m, (F (t (k.val + 1)) - F (t k.val)) ^ 2 / (t (k.val + 1) - t k.val) :=
      coordinate_test_discrete hm y r hr hs j F hF0 hFT
    _ ≤ ∑ k : Fin m, (E (t (k.val + 1)) - E (t k.val)) := by
      exact Finset.sum_le_sum fun k _ => hFE _ (ht _) _ (ht _) (hstep k)
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range (fun k => E (t (k + 1)) - E (t k)) m,
        Finset.sum_range_sub (fun k => E (t k))]
      simp only [t, cumulative_zero, cumulative_end, totalMass]

end KusnerL1
