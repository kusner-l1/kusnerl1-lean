import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-! The ambient space has the `PiLp 1` metric, not the sup metric on functions. -/
namespace KusnerL1
open scoped BigOperators

abbrev L1 (n : ℕ) := PiLp 1 (fun _ : Fin n => ℝ)

theorem l1_dist {n : ℕ} (x y : L1 n) : dist x y = ∑ j, |x j - y j| := by
  simp only [PiLp.dist_eq_of_L1, Real.dist_eq]

def Equilateral {n : ℕ} (S : Set (L1 n)) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y = ρ

def UnitEquilateral {ι : Type*} {n : ℕ} (x : ι → L1 n) : Prop :=
  ∀ i k, i ≠ k → dist (x i) (x k) = 1

theorem unitEquilateral_injective {ι : Type*} {n : ℕ} {x : ι → L1 n}
    (hx : UnitEquilateral x) : Function.Injective x := by
  intro i k hik
  by_contra h
  have H := hx i k h
  rw [hik, dist_self] at H
  norm_num at H

noncomputable def signedBasis {n : ℕ} (p : Fin n × Bool) : L1 n :=
  PiLp.single 1 p.1 (if p.2 then (1 / 2 : ℝ) else -(1 / 2 : ℝ))

theorem signedBasis_unit {n : ℕ} : UnitEquilateral (@signedBasis n) := by
  intro ⟨i, s⟩ ⟨k, t⟩ hik
  by_cases h : i = k
  · subst k
    have hst : s ≠ t := by intro h; exact hik (by simp [h])
    cases s <;> cases t <;> norm_num [signedBasis, PiLp.dist_single_same, Real.dist_eq] at *
  · rw [l1_dist]
    have H : ∀ j : Fin n,
        |signedBasis (i, s) j - signedBasis (k, t) j| =
          (if j = i then (1 / 2 : ℝ) else 0) + (if j = k then (1 / 2 : ℝ) else 0) := by
      intro j
      by_cases hji : j = i
      · subst j
        cases s <;> cases t <;> simp [signedBasis, h]
      · by_cases hjk : j = k
        · subst j
          cases s <;> cases t <;> simp [signedBasis, hji]
        · simp [signedBasis, hji, hjk]
    simp_rw [H, Finset.sum_add_distrib]
    norm_num

/-- The lower bound construction in the Introduction and the main theorem's proof. -/
theorem exists_equilateral_card (n : ℕ) :
    ∃ S : Finset (L1 n), S.card = 2 * n ∧ Equilateral (S : Set (L1 n)) := by
  classical
  let S := Finset.univ.image (@signedBasis n)
  refine ⟨S, ?_, 1, by norm_num, ?_⟩
  · rw [Finset.card_image_of_injective _ (unitEquilateral_injective signedBasis_unit)]
    simp [mul_comm]
  · intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
    exact signedBasis_unit i k (by intro h; exact hxy (congrArg signedBasis h))

/-- Rescaling a positive common distance introduces no restriction on the family. -/
theorem normalize_family {ι : Type*} {n : ℕ} {x : ι → L1 n} {ρ : ℝ}
    (hρ : 0 < ρ) (hx : ∀ i k, i ≠ k → dist (x i) (x k) = ρ) :
    UnitEquilateral (fun i => ρ⁻¹ • x i) := by
  intro i k hik
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ), hx i k hik,
    inv_mul_cancel₀ hρ.ne']

end KusnerL1
