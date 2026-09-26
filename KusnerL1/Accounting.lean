import KusnerL1.Clipping
import KusnerL1.Energy

/-! Accounting for reciprocal masses at original coordinate ends. -/
namespace KusnerL1
open scoped BigOperators
open Finset

/-- A strict first or last gap is precisely a unique original signed end.
`false` denotes the minimum and `true` the maximum. -/
noncomputable def terminalOwner {m : ℕ} (hm : 3 ≤ m) (v : Fin m → ℝ) (s : Bool) : Option (Fin m) :=
  if s then
    if high hm v < v (order v ⟨m - 1, by omega⟩) then some (order v ⟨m - 1, by omega⟩) else none
  else
    if v (order v ⟨0, by omega⟩) < low hm v then some (order v ⟨0, by omega⟩) else none

theorem owner_of_below {m : ℕ} (hm : 3 ≤ m) (v : Fin m → ℝ) {i : Fin m}
    (hi : v i < low hm v) : terminalOwner hm v false = some i := by
  have hr : ((order v).symm i).val = 0 := by
    by_contra H
    have := low_le_of_rank hm v (i := i) (by omega)
    linarith
  have heq : order v ⟨0, by omega⟩ = i := by
    apply (order v).symm.injective
    simp only [Equiv.symm_apply_apply]
    exact Fin.ext hr.symm
  simp [terminalOwner, heq, hi]

theorem owner_of_above {m : ℕ} (hm : 3 ≤ m) (v : Fin m → ℝ) {i : Fin m}
    (hi : high hm v < v i) : terminalOwner hm v true = some i := by
  have hr : ((order v).symm i).val = m - 1 := by
    have hiLt := ((order v).symm i).isLt
    by_contra H
    have := le_high_of_rank hm v (i := i) (by omega)
    linarith
  have heq : order v ⟨m - 1, by omega⟩ = i := by
    apply (order v).symm.injective
    simp only [Equiv.symm_apply_apply]
    exact Fin.ext hr.symm
  simp [terminalOwner, heq, hi]

/-- The strict first gap is equivalent to a unique original minimum. -/
theorem terminalOwner_min_iff {m : ℕ} (hm : 3 ≤ m) (v : Fin m → ℝ) (i : Fin m) :
    terminalOwner hm v false = some i ↔ ∀ k, k ≠ i → v i < v k := by
  constructor
  · intro hi k hki
    simp only [terminalOwner, Bool.false_eq_true, ↓reduceIte] at hi
    split_ifs at hi with h
    have he := Option.some.inj hi
    have hr : 1 ≤ ((order v).symm k).val := by
      by_contra H
      have hk : (order v).symm k = ⟨0, by omega⟩ := by apply Fin.ext; dsimp; omega
      have hk' := congrArg (order v) hk
      simp only [Equiv.apply_symm_apply] at hk'
      exact hki (hk'.trans he)
    rw [← he]
    exact h.trans_le (low_le_of_rank hm v hr)
  · intro hi
    have hi0 : i = order v ⟨0, by omega⟩ := by
      by_contra H
      have H₁ := hi (order v ⟨0, by omega⟩) (Ne.symm H)
      have H₂ : v (order v ⟨0, by omega⟩) ≤ v i := by
        calc
          _ ≤ v (order v ((order v).symm i)) := Tuple.monotone_sort v (by
            change 0 ≤ ((order v).symm i).val; omega)
          _ = _ := congrArg v ((order v).apply_symm_apply i)
      linarith
    apply owner_of_below hm v
    apply hi
    rw [hi0]
    exact (order v).injective.ne (by intro H; have := congrArg Fin.val H; norm_num at this)

/-- The strict last gap is equivalent to a unique original maximum. -/
theorem terminalOwner_max_iff {m : ℕ} (hm : 3 ≤ m) (v : Fin m → ℝ) (i : Fin m) :
    terminalOwner hm v true = some i ↔ ∀ k, k ≠ i → v k < v i := by
  constructor
  · intro hi k hki
    simp only [terminalOwner, ↓reduceIte] at hi
    split_ifs at hi with h
    have he := Option.some.inj hi
    have hr : ((order v).symm k).val ≤ m - 2 := by
      by_contra H
      have hlt := ((order v).symm k).isLt
      have hk : (order v).symm k = ⟨m - 1, by omega⟩ := by apply Fin.ext; dsimp; omega
      have hk' := congrArg (order v) hk
      simp only [Equiv.apply_symm_apply] at hk'
      exact hki (hk'.trans he)
    rw [← he]
    exact (le_high_of_rank hm v hr).trans_lt h
  · intro hi
    have hil : i = order v ⟨m - 1, by omega⟩ := by
      by_contra H
      have H₁ := hi (order v ⟨m - 1, by omega⟩) (Ne.symm H)
      have H₂ : v i ≤ v (order v ⟨m - 1, by omega⟩) := by
        calc
          _ = v (order v ((order v).symm i)) := congrArg v ((order v).apply_symm_apply i).symm
          _ ≤ _ := Tuple.monotone_sort v (by
            change ((order v).symm i).val ≤ m - 1
            have := ((order v).symm i).isLt
            omega)
      linarith
    apply owner_of_above hm v
    apply hi
    rw [hil]
    apply (order v).injective.ne
    intro H
    have := congrArg Fin.val H
    dsimp at this
    omega

theorem moved_owns_end {m : ℕ} (hm : 3 ≤ m) (v : Fin m → ℝ) {i : Fin m}
    (hi : clipped hm v i ≠ v i) : ∃ s, terminalOwner hm v s = some i := by
  by_cases hl : v i < low hm v
  · exact ⟨false, owner_of_below hm v hl⟩
  · have hu : high hm v < v i := by
      by_contra H
      exact hi (clamp_eq (by linarith) (by linarith))
    exact ⟨true, owner_of_above hm v hu⟩

/-- The accounting inequality for an assignment of exceptional labels to ends.
An end has at most one owner, but a label may own several ends. -/
theorem owner_accounting {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (μ : ι → ℝ) (owner : ε → Option ι) (hμ : ∀ i, 2 ≤ μ i)
    (hcover : ∀ i, 2 < μ i → ∃ e, owner e = some i) :
    (∑ i, μ i) ≤ 2 * Fintype.card ι +
      ∑ e, ((match owner e with | none => 2 | some i => μ i) - 2) := by
  classical
  let u := fun e => match owner e with | none => (2 : ℝ) | some i => μ i
  have hu (e : ε) : 0 ≤ u e - 2 := by
    dsimp [u]
    split
    · norm_num
    · exact sub_nonneg.mpr (hμ _)
  have H (i : ι) : μ i - 2 ≤ ∑ e, if owner e = some i then u e - 2 else 0 := by
    by_cases hi : μ i = 2
    · rw [hi, sub_self]
      exact sum_nonneg fun e _ => by split_ifs <;> first | exact hu e | exact le_rfl
    · obtain ⟨e, he⟩ := hcover i (lt_of_le_of_ne (hμ i) (Ne.symm hi))
      have He : u e = μ i := by simp [u, he]
      calc
        μ i - 2 = (if owner e = some i then u e - 2 else 0) := by rw [if_pos he, He]
        _ ≤ _ := Finset.single_le_sum (f := fun e => if owner e = some i then u e - 2 else 0)
          (fun e _ => by split_ifs <;> first | exact hu e | exact le_rfl) (mem_univ e)
  have Hsum := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => H i)
  rw [sum_comm] at Hsum
  have He (e : ε) : (∑ i, if owner e = some i then u e - 2 else 0) = u e - 2 := by
    cases h : owner e with
    | none => simp [h, u]
    | some i => simp
  simp_rw [He] at Hsum
  simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul] at Hsum
  change (∑ i, μ i) ≤ 2 * (Fintype.card ι : ℝ) + (∑ e, (u e - 2))
  simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
  linarith

theorem clipped_mass_bounds {n : ℕ} (hn : 2 ≤ n) {x : Fin (2 * n + 1) → L1 n}
    (hx : UnitEquilateral x) (i : Fin (2 * n + 1)) :
    2 ≤ mass (radius (by omega) x) i ∧
      mass (radius (by omega) x) i ≤ 2 * ((n : ℝ) - 1) := by
  have hp := clipping_radius_pos hn hx i
  have hb := clipping_radius_bounds hn hx i
  have hm : 0 < mass (radius (by omega) x) i := inv_pos.mpr hp
  have he : mass (radius (by omega) x) i * radius (by omega) x i = 1 := inv_mul_cancel₀ hp.ne'
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · nlinarith
  · have hlow := (div_le_iff₀ (by linarith : 0 < 2 * ((n : ℝ) - 1))).mp hb.1
    have H := mul_le_mul_of_nonneg_left hlow hm.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hb.1) hm.le]

/-- Every label of reciprocal mass greater than two owns an original end. -/
theorem heavy_label_owns_end {n : ℕ} (hn : 2 ≤ n) {x : Fin (2 * n + 1) → L1 n}
    (hx : UnitEquilateral x) (i : Fin (2 * n + 1))
    (hi : 2 < mass (radius (by omega) x) i) :
    ∃ e : Fin n × Bool, terminalOwner (by omega) (fun k => x k e.1) e.2 = some i := by
  have hp := clipping_radius_pos hn hx i
  have he : mass (radius (by omega) x) i * radius (by omega) x i = 1 := inv_mul_cancel₀ hp.ne'
  have hs : 0 < displacement (by omega) x i := by
    have : radius (by omega) x i < 1 / 2 := by nlinarith
    unfold radius at this
    linarith
  have hm : ∃ j, terminalClipping (by omega) x i j ≠ x i j := by
    by_contra H
    push Not at H
    have : displacement (by omega) x i = 0 := by simp only [displacement, H, sub_self, abs_zero, sum_const_zero]
    linarith
  obtain ⟨j, hj⟩ := hm
  obtain ⟨s, howner⟩ := moved_owns_end (by omega) (fun k => x k j) hj
  exact ⟨(j, s), howner⟩

noncomputable def assignedMass {n : ℕ} (hn : 2 ≤ n) (x : Fin (2 * n + 1) → L1 n)
    (e : Fin n × Bool) : ℝ :=
  match terminalOwner (by omega) (fun k => x k e.1) e.2 with
  | none => 2
  | some i => mass (radius (by omega) x) i

/-- Equation `eq:mass-accounting`, before replacing the endpoint sum by `2 n z`. -/
theorem mass_accounting {n : ℕ} (hn : 2 ≤ n) {x : Fin (2 * n + 1) → L1 n}
    (hx : UnitEquilateral x) :
    totalMass (radius (by omega) x) ≤ (∑ e, assignedMass hn x e) + 2 := by
  have H := owner_accounting (mass (radius (by omega) x))
    (fun e : Fin n × Bool => terminalOwner (by omega) (fun k => x k e.1) e.2)
    (fun i => (clipped_mass_bounds hn hx i).1) (heavy_label_owns_end hn hx)
  unfold totalMass assignedMass
  simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
    Fintype.card_prod, Fintype.card_bool, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat] at H
  convert H using 1
  ring_nf
  congr 1
  apply sum_congr rfl
  intro e _
  split <;> split <;> simp_all

end KusnerL1
