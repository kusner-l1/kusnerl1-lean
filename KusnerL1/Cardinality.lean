import KusnerL1.Metric
import Mathlib.Data.Fintype.EquivFin

/-! Passage between arbitrary equilateral sets and finite unit families.
These implications do not supply the geometric upper-bound exclusion. -/
namespace KusnerL1

/-- Extended cardinalities retain infinite sets instead of assigning them zero.
Once an upper bound is established this supremum is the usual equilateral dimension. -/
noncomputable def equilateralDimension (n : ℕ) : ℕ∞ :=
  sSup {k | ∃ S : Set (L1 n), Equilateral S ∧ S.encard = k}

theorem equilateralDimension_lower (n : ℕ) : (2 * n : ℕ) ≤ equilateralDimension n := by
  obtain ⟨S, hc, he⟩ := exists_equilateral_card n
  apply le_sSup
  exact ⟨S, he, by simpa using congrArg (fun k : ℕ => (k : ℕ∞)) hc⟩

/-- No finiteness hypothesis on `S` is needed. -/
theorem equilateral_encard_le_of_exclusion {n N : ℕ}
    (hex : ∀ x : Fin (N + 1) → L1 n, ¬ UnitEquilateral x)
    {S : Set (L1 n)} (hS : Equilateral S) : S.encard ≤ N := by
  classical
  by_contra H
  have hlt : (N : ℕ∞) < S.encard := lt_of_not_ge H
  have hle : ((N + 1 : ℕ) : ℕ∞) ≤ S.encard := by
    simpa using ENat.natCast_add_one_le_iff.mpr hlt
  obtain ⟨t, htS, htc⟩ := Set.exists_subset_encard_eq hle
  have htfin := Set.finite_of_encard_eq_coe htc
  let : Fintype t := htfin.fintype
  have hcard : Fintype.card t = N + 1 := by
    have H : (Fintype.card t : ℕ∞) = N + 1 := by
      change ENat.card t = _ at htc
      rw [ENat.card_eq_coe_fintype_card] at htc
      exact htc
    exact_mod_cast H
  let e : t ≃ Fin (N + 1) := Fintype.equivFinOfCardEq hcard
  let x : Fin (N + 1) → L1 n := fun i => (e.symm i).val
  obtain ⟨ρ, hρ, hdist⟩ := hS
  have hx : ∀ i k, i ≠ k → dist (x i) (x k) = ρ := by
    intro i k hik
    apply hdist _ (htS (e.symm i).property) _ (htS (e.symm k).property)
    intro heq
    apply hik
    exact e.symm.injective (Subtype.ext heq)
  exact hex _ (normalize_family hρ hx)

theorem equilateral_finite_of_exclusion {n N : ℕ}
    (hex : ∀ x : Fin (N + 1) → L1 n, ¬ UnitEquilateral x)
    {S : Set (L1 n)} (hS : Equilateral S) : S.Finite ∧ S.ncard ≤ N :=
  Set.encard_le_coe_iff_finite_ncard_le.mp (equilateral_encard_le_of_exclusion hex hS)

/-- The final step of the main theorem, conditional on the required exclusion.
This theorem is not an unconditional upper bound in any dimension. -/
theorem equilateralDimension_eq_of_exclusion (n : ℕ)
    (hex : ∀ x : Fin (2 * n + 1) → L1 n, ¬ UnitEquilateral x) :
    equilateralDimension n = (2 * n : ℕ) := by
  apply le_antisymm _ (equilateralDimension_lower n)
  apply sSup_le
  rintro k ⟨S, he, rfl⟩
  exact equilateral_encard_le_of_exclusion hex he

end KusnerL1
