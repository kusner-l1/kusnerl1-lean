import KusnerL1.Accounting
import KusnerL1.CoordinateBounds

/-! Residual endpoint groups and spans in Lemma `lem:endpoint-accounting`. -/
namespace KusnerL1
open scoped BigOperators
open Finset

lemma clipped_minValue {m : ℕ} (hm : 3 ≤ m) (v : Fin m → ℝ) :
    minValue (by omega) (clipped hm v) = low hm v := by
  obtain ⟨i, k, hik, hi, hk⟩ := clipped_low_twice hm v
  apply le_antisymm
  · exact hi ▸ minValue_le (by omega) (clipped hm v) i
  · exact (clipped_mem hm v _).1

lemma clipped_maxValue {m : ℕ} (hm : 3 ≤ m) (v : Fin m → ℝ) :
    maxValue (by omega) (clipped hm v) = high hm v := by
  obtain ⟨i, k, hik, hi, hk⟩ := clipped_high_twice hm v
  apply le_antisymm
  · exact (clipped_mem hm v _).2
  · exact hi ▸ le_maxValue (by omega) (clipped hm v) i

noncomputable def residualEnd {m : ℕ} (hm : 3 ≤ m) (v : Fin m → ℝ) (s : Bool) : ℝ :=
  if s then high hm v else low hm v

lemma residualEnd_twice {m : ℕ} (hm : 3 ≤ m) (v : Fin m → ℝ) (s : Bool) :
    ∃ i k, i ≠ k ∧ clipped hm v i = residualEnd hm v s ∧
      clipped hm v k = residualEnd hm v s := by
  cases s
  · exact clipped_low_twice hm v
  · exact clipped_high_twice hm v

lemma owner_stays {m : ℕ} (hm : 3 ≤ m) (v : Fin m → ℝ) (s : Bool) {i : Fin m}
    (hi : terminalOwner hm v s = some i) : clipped hm v i = residualEnd hm v s := by
  cases s
  · simp only [terminalOwner, Bool.false_eq_true, ↓reduceIte] at hi
    split_ifs at hi with h
    · have he := Option.some.inj hi
      rw [← he]
      exact clamp_low (low_le_high hm v) h.le
  · simp only [terminalOwner, ↓reduceIte] at hi
    split_ifs at hi with h
    · have he := Option.some.inj hi
      rw [← he]
      exact clamp_high (low_le_high hm v) h.le

lemma two_mass_le {m : ℕ} (v μ : Fin m → ℝ) (hμ : ∀ i, 0 ≤ μ i) {c : ℝ}
    {i k : Fin m} (hik : i ≠ k) (hi : v i = c) (hk : v k = c) :
    μ i + μ k ≤ ∑ a ∈ univ.filter (fun a => v a = c), μ a := by
  classical
  have H : ∑ a ∈ ({i, k} : Finset (Fin m)), μ a ≤ ∑ a ∈ univ.filter (fun a => v a = c), μ a := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro a ha
      simp only [mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl <;> simp [hi, hk]
    · intro a _ _; exact hμ a
  simpa [hik] using H

noncomputable def residualMass {n : ℕ} (hn : 2 ≤ n) (x : Fin (2 * n + 1) → L1 n)
    (e : Fin n × Bool) : ℝ :=
  ∑ i ∈ univ.filter (fun i => clipped (by omega) (fun k => x k e.1) i =
    residualEnd (by omega) (fun k => x k e.1) e.2), mass (radius (by omega) x) i

/-- Both residual endpoint groups contain the assigned mass plus at least two. -/
theorem residualMass_lower {n : ℕ} (hn : 2 ≤ n) {x : Fin (2 * n + 1) → L1 n}
    (hx : UnitEquilateral x) (e : Fin n × Bool) : assignedMass hn x e + 2 ≤ residualMass hn x e := by
  have hμ := fun i => (clipped_mass_bounds hn hx i).1
  have hp : ∀ i, 0 ≤ mass (radius (by omega) x) i := fun i => by linarith [hμ i]
  obtain ⟨a, b, hab, ha, hb⟩ := residualEnd_twice (by omega) (fun k => x k e.1) e.2
  unfold assignedMass
  split
  · have H := two_mass_le _ _ hp hab ha hb
    change _ ≤ residualMass hn x e at H
    linarith [hμ a, hμ b]
  · rename_i i hi
    have hi' := owner_stays (by omega) (fun k => x k e.1) e.2 hi
    by_cases hia : i = a
    · subst i
      have H := two_mass_le _ _ hp hab ha hb
      change _ ≤ residualMass hn x e at H
      linarith [hμ b]
    · have H := two_mass_le _ _ hp hia hi' ha
      change _ ≤ residualMass hn x e at H
      linarith [hμ a]

lemma residualMass_min {n : ℕ} (hn : 2 ≤ n) (x : Fin (2 * n + 1) → L1 n) (j : Fin n) :
    residualMass hn x (j, false) = minMass (by omega)
      (fun i => terminalClipping (by omega) x i j) (mass (radius (by omega) x)) := by
  simp only [residualMass, minMass, terminalClipping_apply, clipped_minValue, residualEnd, Bool.false_eq_true, ↓reduceIte]

lemma residualMass_max {n : ℕ} (hn : 2 ≤ n) (x : Fin (2 * n + 1) → L1 n) (j : Fin n) :
    residualMass hn x (j, true) = maxMass (by omega)
      (fun i => terminalClipping (by omega) x i j) (mass (radius (by omega) x)) := by
  simp only [residualMass, maxMass, terminalClipping_apply, clipped_maxValue, residualEnd, ↓reduceIte]

noncomputable def maxWeight {n : ℕ} (hn : 2 ≤ n) (x : Fin (2 * n + 1) → L1 n) : ℝ :=
  univ.sup' univ_nonempty (mass (radius (by omega) x))

lemma mass_le_maxWeight {n : ℕ} (hn : 2 ≤ n) (x : Fin (2 * n + 1) → L1 n) (i : Fin (2 * n + 1)) :
    mass (radius (by omega) x) i ≤ maxWeight hn x := le_sup' _ (mem_univ i)

lemma maxWeight_attained {n : ℕ} (hn : 2 ≤ n) (x : Fin (2 * n + 1) → L1 n) :
    ∃ i, maxWeight hn x = mass (radius (by omega) x) i := by
  obtain ⟨i, _, hi⟩ := exists_mem_eq_sup' univ_nonempty (mass (radius (by omega) x))
  exact ⟨i, hi⟩

lemma maxWeight_bounds {n : ℕ} (hn : 2 ≤ n) {x : Fin (2 * n + 1) → L1 n} (hx : UnitEquilateral x) :
    2 ≤ maxWeight hn x ∧ maxWeight hn x ≤ 2 * ((n : ℝ) - 1) := by
  obtain ⟨i, hi⟩ := maxWeight_attained hn x
  rw [hi]
  exact clipped_mass_bounds hn hx i

lemma assignedMass_bounds {n : ℕ} (hn : 2 ≤ n) {x : Fin (2 * n + 1) → L1 n}
    (hx : UnitEquilateral x) (e : Fin n × Bool) :
    2 ≤ assignedMass hn x e ∧ assignedMass hn x e ≤ maxWeight hn x := by
  unfold assignedMass
  split
  · exact ⟨le_rfl, (maxWeight_bounds hn hx).1⟩
  · exact ⟨(clipped_mass_bounds hn hx _).1, mass_le_maxWeight hn x _⟩

lemma clipped_totalMass_lower {n : ℕ} (hn : 2 ≤ n) {x : Fin (2 * n + 1) → L1 n}
    (hx : UnitEquilateral x) : 2 * (2 * (n : ℝ) + 1) ≤ totalMass (radius (by omega) x) := by
  have H := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin (2 * n + 1)))) =>
    (clipped_mass_bounds hn hx i).1)
  simpa [totalMass, mul_comm] using H

lemma assignedMass_lt_half {n : ℕ} (hn : 2 ≤ n) {x : Fin (2 * n + 1) → L1 n}
    (hx : UnitEquilateral x) (e : Fin n × Bool) :
    assignedMass hn x e + 2 < totalMass (radius (by omega) x) / 2 := by
  have := clipped_totalMass_lower hn hx
  have := (assignedMass_bounds hn hx e).2
  have := (maxWeight_bounds hn hx).2
  linarith

noncomputable def residualSpan {n : ℕ} (hn : 2 ≤ n) (x : Fin (2 * n + 1) → L1 n) (j : Fin n) : ℝ :=
  high (by omega) (fun i => x i j) - low (by omega) (fun i => x i j)

lemma residualSpan_eq {n : ℕ} (hn : 2 ≤ n) (x : Fin (2 * n + 1) → L1 n) (j : Fin n) :
    residualSpan hn x j = maxValue (by omega) (fun i => terminalClipping (by omega) x i j) -
      minValue (by omega) (fun i => terminalClipping (by omega) x i j) := by
  simp only [terminalClipping_apply, clipped_maxValue, clipped_minValue, residualSpan]

lemma residualSpan_nonneg {n : ℕ} (hn : 2 ≤ n) (x : Fin (2 * n + 1) → L1 n) (j : Fin n) :
    0 ≤ residualSpan hn x j := sub_nonneg.mpr (low_le_high (by omega) _)

lemma span_le_radius_of_end {n : ℕ} (hn : 2 ≤ n) {x : Fin (2 * n + 1) → L1 n}
    (hx : UnitEquilateral x) (e : Fin n × Bool) {i : Fin (2 * n + 1)}
    (hi : clipped (by omega) (fun k => x k e.1) i = residualEnd (by omega) (fun k => x k e.1) e.2) :
    residualSpan hn x e.1 ≤ radius (by omega) x i := by
  obtain ⟨a, b, hab, ha, hb⟩ := clipped_low_twice (by omega) (fun k => x k e.1)
  obtain ⟨c, d, hcd, hc, hd⟩ := clipped_high_twice (by omega) (fun k => x k e.1)
  have H₁ := coordinate_le_radius (by omega) x hx i a e.1
  have H₂ := coordinate_le_radius (by omega) x hx i c e.1
  simp only [terminalClipping_apply, hi, ha, hc] at H₁ H₂
  rcases e with ⟨j, s⟩
  cases s <;> simp only [residualEnd, Bool.false_eq_true, ↓reduceIte] at H₁ H₂
  · exact (le_abs_self _).trans (by simpa only [abs_sub_comm, residualSpan] using H₂)
  · exact (le_abs_self _).trans H₁

/-- The two individual endpoint span bounds in `eq:endpoint-span`. -/
theorem residualSpan_le_assigned {n : ℕ} (hn : 2 ≤ n) {x : Fin (2 * n + 1) → L1 n}
    (hx : UnitEquilateral x) (e : Fin n × Bool) :
    residualSpan hn x e.1 ≤ 1 / assignedMass hn x e := by
  unfold assignedMass
  split
  · obtain ⟨i, k, hik, hi, hk⟩ := residualEnd_twice (by omega) (fun k => x k e.1) e.2
    exact (span_le_radius_of_end hn hx e hi).trans (radius_le_half (by omega) x i)
  · rename_i i hi
    simpa only [mass, one_div, inv_inv] using
      span_le_radius_of_end hn hx e (owner_stays (by omega) (fun k => x k e.1) e.2 hi)

/-- The maximum-mass span bound in `eq:endpoint-span`. -/
theorem residualSpan_le_maxWeight {n : ℕ} (hn : 2 ≤ n) {x : Fin (2 * n + 1) → L1 n}
    (hx : UnitEquilateral x) (j : Fin n) : residualSpan hn x j ≤ 2 / maxWeight hn x := by
  obtain ⟨p, hp⟩ := maxWeight_attained hn x
  obtain ⟨a, b, hab, ha, hb⟩ := clipped_low_twice (by omega) (fun k => x k j)
  obtain ⟨c, d, hcd, hc, hd⟩ := clipped_high_twice (by omega) (fun k => x k j)
  have H₁ := coordinate_le_radius (by omega) x hx p a j
  have H₂ := coordinate_le_radius (by omega) x hx p c j
  simp only [terminalClipping_apply, ha, hc, abs_le] at H₁ H₂
  rw [hp, div_eq_mul_inv, mass, inv_inv]
  unfold residualSpan
  linarith

end KusnerL1
