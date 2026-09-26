import KusnerL1.Averaging

/-! From an arbitrary unit equilateral family to the scalar obstruction. -/
set_option maxHeartbeats 800000

namespace KusnerL1
open scoped BigOperators
open Finset Real

noncomputable def logOdds (T a : ℝ) : ℝ := log (T - a) - log a

lemma logOdds_antitone {T a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    logOdds T b ≤ logOdds T a := by
  have H₁ := log_le_log (sub_pos.mpr hbT) (show T - b ≤ T - a by linarith)
  have H₂ := log_le_log ha hab
  unfold logOdds
  linarith

lemma logOdds_nonneg {T a : ℝ} (ha : 0 < a) (haT : a ≤ T / 2) : 0 ≤ logOdds T a :=
  sub_nonneg.mpr (log_le_log ha (by linarith))

lemma constant_cutEnergy {m n : ℕ} (hm : 0 < m) (y : Fin m → L1 n) (r : Fin m → ℝ)
    (j : Fin n) (hc : minValue hm (fun i => y i j) = maxValue hm (fun i => y i j)) :
    cutEnergy hm y r j = 0 := by
  apply sum_eq_zero
  intro k _
  have H₁ := orderedValue_mono hm (fun i => y i j) (Nat.zero_le k.val)
  have H₂ := orderedValue_le_max hm (fun i => y i j) (k.val + 1)
  have Hg := gap_nonneg hm (fun i => y i j) k
  have Hz : gap hm (fun i => y i j) k = 0 := by
    dsimp only [gap, minValue, maxValue] at *
    linarith
  rw [Hz, zero_mul]

/-- Equation `eq:assigned-endpoint-energy`, also for constant coordinates. -/
theorem assigned_endpoint_energy {n : ℕ} (hn : 2 ≤ n) {x : Fin (2 * n + 1) → L1 n}
    (hx : UnitEquilateral x) (j : Fin n) :
    cutEnergy (by omega) (terminalClipping (by omega) x) (radius (by omega) x) j ≤
      1 + 1 / 4 * (logOdds (totalMass (radius (by omega) x)) (assignedMass hn x (j, false) + 2) +
        logOdds (totalMass (radius (by omega) x)) (assignedMass hn x (j, true) + 2)) := by
  let y := terminalClipping (by omega) x
  let r := radius (by omega) x
  let T := totalMass r
  let A := minMass (by omega) (fun i => y i j) (mass r)
  let B := maxMass (by omega) (fun i => y i j) (mass r)
  have hr : ∀ i, 0 < r i := clipping_radius_pos hn hx
  have hs : Star y r := fun _ _ hik => clipping_star (by omega) x hx hik
  have hu (s : Bool) : 0 < assignedMass hn x (j, s) + 2 := by
    linarith [(assignedMass_bounds hn hx (j, s)).1]
  have hhalf (s : Bool) : assignedMass hn x (j, s) + 2 < T / 2 := assignedMass_lt_half hn hx (j, s)
  have hminmax : minValue (by omega) (fun i => y i j) ≤ maxValue (by omega) (fun i => y i j) :=
    (minValue_le (by omega) (fun i => y i j) ⟨0, by omega⟩).trans (le_maxValue (by omega) (fun i => y i j) _)
  rcases hminmax.eq_or_lt with hc | hc
  · rw [constant_cutEnergy (by omega) y r j hc]
    have H₁ := logOdds_nonneg (hu false) (hhalf false).le
    have H₂ := logOdds_nonneg (hu true) (hhalf true).le
    linarith
  · have hA : 0 < A := minMass_pos (by omega) _ _ (fun i => inv_pos.mpr (hr i))
    have hB : 0 < B := maxMass_pos (by omega) _ _ (fun i => inv_pos.mpr (hr i))
    have hAB : A + B ≤ T := endpointMass_sum_le (by omega) _ _ (fun i => (inv_pos.mpr (hr i)).le) hc
    have hTA : 0 < T - A := by linarith
    have hTB : 0 < T - B := by linarith
    have HA : assignedMass hn x (j, false) + 2 ≤ A := by
      simpa only [residualMass_min] using residualMass_lower hn hx (j, false)
    have HB : assignedMass hn x (j, true) + 2 ≤ B := by
      simpa only [residualMass_max] using residualMass_lower hn hx (j, true)
    have H := endpoint_energy_bound (by omega) y r hr hs j hc
    change _ ≤ 1 + 1 / 4 * log (((T - A) * (T - B)) / (A * B)) at H
    rw [log_div (mul_pos hTA hTB).ne' (mul_pos hA hB).ne', log_mul hTA.ne' hTB.ne',
      log_mul hA.ne' hB.ne'] at H
    have H₁ := logOdds_antitone (hu false) HA (by linarith : A < T)
    have H₂ := logOdds_antitone (hu true) HB (by linarith : B < T)
    unfold logOdds at H₁ H₂ ⊢
    linarith

noncomputable def meanAssigned {n : ℕ} (hn : 2 ≤ n) (x : Fin (2 * n + 1) → L1 n) : ℝ :=
  (∑ e, assignedMass hn x e) / (2 * n)

lemma sum_assignedMass {n : ℕ} (hn : 2 ≤ n) (x : Fin (2 * n + 1) → L1 n) :
    ∑ e, assignedMass hn x e = 2 * n * meanAssigned hn x := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold meanAssigned
  field_simp

lemma meanAssigned_bounds {n : ℕ} (hn : 2 ≤ n) {x : Fin (2 * n + 1) → L1 n}
    (hx : UnitEquilateral x) : 2 ≤ meanAssigned hn x ∧ meanAssigned hn x ≤ maxWeight hn x := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have Hl := sum_le_sum (fun e (_ : e ∈ (univ : Finset (Fin n × Bool))) => (assignedMass_bounds hn hx e).1)
  have Hu := sum_le_sum (fun e (_ : e ∈ (univ : Finset (Fin n × Bool))) => (assignedMass_bounds hn hx e).2)
  simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Nat.cast_mul, Nat.cast_ofNat, nsmul_eq_mul, sum_assignedMass hn x] at Hl Hu
  constructor <;> nlinarith

/-- Proposition `prop:average-endpoint` for the clipped family. -/
theorem average_endpoint {n : ℕ} (hn : 2 ≤ n) {x : Fin (2 * n + 1) → L1 n}
    (hx : UnitEquilateral x) :
    (∑ j, cutEnergy (by omega) (terminalClipping (by omega) x) (radius (by omega) x) j) / n ≤
      1 + 1 / 2 * G n (maxWeight hn x) (meanAssigned hn x) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let T := totalMass (radius (by omega) x)
  let u := assignedMass hn x
  have H := sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin n))) => assigned_endpoint_energy hn hx j)
  have Hlog := average_endpoint_logs (show 0 < n by omega) u (assignedMass_bounds hn hx)
    (sum_assignedMass hn x) (meanAssigned_bounds hn hx).1
    (by simpa only [← sum_assignedMass] using mass_accounting hn hx)
    (fun e => by have := assignedMass_lt_half hn hx e; have := (assignedMass_bounds hn hx e).1; dsimp [u, T]; linarith)
  have heq : (∑ j, (logOdds T (u (j, false) + 2) + logOdds T (u (j, true) + 2))) =
      ∑ e, (log (T - u e - 2) - log (u e + 2)) := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, logOdds, sub_add_eq_sub_sub, sub_right_comm, add_comm]
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, ← mul_sum] at H
  rw [← sum_add_distrib] at H
  change _ ≤ n + 1 / 4 * (∑ j, (logOdds T (u (j, false) + 2) + logOdds T (u (j, true) + 2))) at H
  rw [heq] at H
  have Hlog' := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mp Hlog
  apply (div_le_iff₀ hnR).mpr
  nlinarith

/-- Corollary `cor:scalar-obstruction`, with no extra geometric hypotheses. -/
theorem scalar_obstruction {n : ℕ} (hn : 2 ≤ n) {x : Fin (2 * n + 1) → L1 n}
    (hx : UnitEquilateral x) :
    ScalarConditions n (maxWeight hn x) (meanAssigned hn x / maxWeight hn x) := by
  let M := maxWeight hn x
  let z := meanAssigned hn x
  let r := radius (by omega) x
  let y := terminalClipping (by omega) x
  let T := totalMass r
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hM := maxWeight_bounds hn hx
  have hz := meanAssigned_bounds hn hx
  have hMp : 0 < M := by dsimp [M]; linarith
  have hr : ∀ i, 0 < r i := clipping_radius_pos hn hx
  have hs : Star y r := fun _ _ hik => clipping_star (by omega) x hx hik
  have hT : 0 < T := totalMass_pos r hr
  have hsum : ∑ j, cutEnergy (by omega) y r j = 2 * n := by
    simpa using total_cutEnergy (by omega) y r hr hs
  have hzw : M * (z / M) = z := by field_simp
  refine ⟨⟨hM.1, hM.2, (div_le_div_iff_of_pos_right hMp).mpr hz.1, (div_le_one hMp).mpr hz.2⟩, ?_, ?_⟩
  · intro R hR
    have H := sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin n))) => span_energy_bound (by omega) y r hr hs j hR)
    dsimp only [y] at H
    simp_rw [← residualSpan_eq hn x] at H
    rw [hsum, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum] at H
    have Havg := average_span (show 0 < n by omega) (assignedMass hn x) (residualSpan hn x)
      hT.le hMp hz.1 hz.2
      (fun e => ⟨by linarith [(assignedMass_bounds hn hx e).1], (assignedMass_bounds hn hx e).2⟩)
      (sum_assignedMass hn x) (by simpa only [← sum_assignedMass] using mass_accounting hn hx)
      (residualSpan_le_assigned hn hx) (residualSpan_le_maxWeight hn hx)
    have Havg' := (div_le_iff₀ hnR).mp
      (show (T * ∑ j, residualSpan hn x j) / n ≤ Phi n M (z / M) by convert Havg using 1; ring)
    have hb : 0 ≤ b R := by unfold b; positivity
    have Hmul := mul_le_mul_of_nonneg_left Havg' hb
    change 2 ≤ a R + b R * Phi n M (z / M)
    have Hfinal : (2 : ℝ) * n ≤ (a R + b R * Phi n M (z / M)) * n := by
      dsimp only [T, r] at Hmul
      nlinarith
    exact (mul_le_mul_iff_left₀ hnR).mp Hfinal
  · have H := average_endpoint hn hx
    change _ ≤ 1 + 1 / 2 * G n M z at H
    rw [hsum] at H
    have hdiv : (2 * n : ℝ) / n = 2 := by field_simp
    rw [hdiv] at H
    change 2 ≤ 1 + 1 / 2 * G n M (M * (z / M))
    rwa [hzw]

end KusnerL1
