import KusnerL1.Metric
import Mathlib.Data.Fin.Tuple.Sort

/-! Simultaneous terminal clipping, as in Definition `def:clipping`. -/
namespace KusnerL1
open scoped BigOperators

noncomputable def clamp (l u t : ℝ) : ℝ := min u (max l t)

theorem clamp_mem {l u t : ℝ} (hlu : l ≤ u) : l ≤ clamp l u t ∧ clamp l u t ≤ u := by
  exact ⟨le_min hlu (le_max_left _ _), min_le_left _ _⟩

theorem clamp_eq {l u t : ℝ} (hl : l ≤ t) (hu : t ≤ u) : clamp l u t = t := by
  simp [clamp, max_eq_right hl, min_eq_right hu]

theorem clamp_low {l u t : ℝ} (hlu : l ≤ u) (ht : t ≤ l) : clamp l u t = l := by
  simp [clamp, max_eq_left ht, min_eq_right hlu]

theorem clamp_high {l u t : ℝ} (hlu : l ≤ u) (ht : u ≤ t) : clamp l u t = u := by
  simp [clamp, max_eq_right (hlu.trans ht), min_eq_left ht]

/-- A pair loses exactly the displacements of its two ends, provided the pair
cannot lie together strictly outside either terminal threshold. -/
theorem clamp_distance {l u s t : ℝ} (hlu : l ≤ u)
    (hl : l ≤ max s t) (hu : min s t ≤ u) :
    |clamp l u s - clamp l u t| = |s - t| - |s - clamp l u s| - |t - clamp l u t| := by
  unfold clamp
  grind [abs_eq_max_neg]

section Ordered
variable {m : ℕ} (hm : 3 ≤ m) (v : Fin m → ℝ)

noncomputable def order : Equiv.Perm (Fin m) := Tuple.sort v
noncomputable def low : ℝ := v (order v ⟨1, by omega⟩)
noncomputable def high : ℝ := v (order v ⟨m - 2, by omega⟩)
noncomputable def clipped (i : Fin m) : ℝ := clamp (low hm v) (high hm v) (v i)

theorem low_le_high : low hm v ≤ high hm v := by
  apply Tuple.monotone_sort v
  change 1 ≤ m - 2
  omega

theorem clipped_mem (i : Fin m) : low hm v ≤ clipped hm v i ∧ clipped hm v i ≤ high hm v :=
  clamp_mem (low_le_high hm v)

theorem low_le_of_rank {i : Fin m} (hi : 1 ≤ ((order v).symm i).val) : low hm v ≤ v i := by
  have H := Tuple.monotone_sort v (show (⟨1, by omega⟩ : Fin m) ≤ (order v).symm i from hi)
  simpa [low, order] using H

theorem le_high_of_rank {i : Fin m} (hi : ((order v).symm i).val ≤ m - 2) : v i ≤ high hm v := by
  have H := Tuple.monotone_sort v (show (order v).symm i ≤ (⟨m - 2, by omega⟩ : Fin m) from hi)
  simpa [high, order] using H

theorem clipped_eq_of_not_terminal {i : Fin m}
    (hi0 : i ≠ order v ⟨0, by omega⟩) (hil : i ≠ order v ⟨m - 1, by omega⟩) :
    clipped hm v i = v i := by
  have hr0 : ((order v).symm i).val ≠ 0 := by
    intro H
    apply hi0
    apply (order v).symm.injective
    simpa using (Fin.ext H)
  have hrl : ((order v).symm i).val ≠ m - 1 := by
    intro H
    apply hil
    apply (order v).symm.injective
    simpa using (Fin.ext H)
  exact clamp_eq (low_le_of_rank hm v (by omega)) (le_high_of_rank hm v (by omega))

theorem clipped_distance {i k : Fin m} (hik : i ≠ k) :
    |clipped hm v i - clipped hm v k| = |v i - v k| -
      |v i - clipped hm v i| - |v k - clipped hm v k| := by
  apply clamp_distance (low_le_high hm v)
  · by_cases hi : 1 ≤ ((order v).symm i).val
    · exact (low_le_of_rank hm v hi).trans (le_max_left _ _)
    · have hk : 1 ≤ ((order v).symm k).val := by
        by_contra H
        apply hik
        apply (order v).symm.injective
        apply Fin.ext
        omega
      exact (low_le_of_rank hm v hk).trans (le_max_right _ _)
  · by_cases hi : ((order v).symm i).val ≤ m - 2
    · exact (min_le_left _ _).trans (le_high_of_rank hm v hi)
    · have hk : ((order v).symm k).val ≤ m - 2 := by
        by_contra H
        apply hik
        apply (order v).symm.injective
        apply Fin.ext
        have := ((order v).symm i).isLt
        have := ((order v).symm k).isLt
        omega
      exact (min_le_right _ _).trans (le_high_of_rank hm v hk)

theorem clipped_low_twice : ∃ i k : Fin m, i ≠ k ∧
    clipped hm v i = low hm v ∧ clipped hm v k = low hm v := by
  refine ⟨order v ⟨0, by omega⟩, order v ⟨1, by omega⟩, ?_, ?_, ?_⟩
  · exact (order v).injective.ne (by intro H; have := congrArg Fin.val H; norm_num at this)
  · apply clamp_low (low_le_high hm v)
    exact Tuple.monotone_sort v (by change (0 : ℕ) ≤ 1; omega)
  · exact clamp_low (low_le_high hm v) le_rfl

theorem clipped_high_twice : ∃ i k : Fin m, i ≠ k ∧
    clipped hm v i = high hm v ∧ clipped hm v k = high hm v := by
  refine ⟨order v ⟨m - 2, by omega⟩, order v ⟨m - 1, by omega⟩, ?_, ?_, ?_⟩
  · apply (order v).injective.ne
    intro H
    have := congrArg Fin.val H
    dsimp at this
    omega
  · exact clamp_high (low_le_high hm v) le_rfl
  · apply clamp_high (low_le_high hm v)
    exact Tuple.monotone_sort v (by change m - 2 ≤ m - 1; omega)

theorem original_min_stays {i : Fin m} (hi : ∀ k, v i ≤ v k) :
    clipped hm v i = low hm v := clamp_low (low_le_high hm v) (hi _)

theorem original_max_stays {i : Fin m} (hi : ∀ k, v k ≤ v i) :
    clipped hm v i = high hm v := clamp_high (low_le_high hm v) (hi _)
end Ordered

section Family
variable {m n : ℕ} (hm : 3 ≤ m) (x : Fin m → L1 n)

noncomputable def terminalClipping (i : Fin m) : L1 n :=
  WithLp.toLp 1 (fun j => clipped hm (fun k => x k j) i)
noncomputable def displacement (i : Fin m) : ℝ :=
  ∑ j, |x i j - terminalClipping hm x i j|
noncomputable def radius (i : Fin m) : ℝ := 1 / 2 - displacement hm x i

@[simp] theorem terminalClipping_apply (i : Fin m) (j : Fin n) :
    terminalClipping hm x i j = clipped hm (fun k => x k j) i := rfl

theorem clipping_star (hx : UnitEquilateral x) {i k : Fin m} (hik : i ≠ k) :
    dist (terminalClipping hm x i) (terminalClipping hm x k) = radius hm x i + radius hm x k := by
  have H := hx i k hik
  rw [l1_dist] at H ⊢
  simp_rw [terminalClipping_apply, clipped_distance hm _ hik,
    Finset.sum_sub_distrib]
  rw [H]
  unfold radius displacement
  simp only [terminalClipping_apply]
  ring

theorem radius_le_half (i : Fin m) : radius hm x i ≤ 1 / 2 := by
  have : 0 ≤ displacement hm x i := Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold radius
  linarith

theorem radius_nonneg (hx : UnitEquilateral x) (i : Fin m) : 0 ≤ radius hm x i := by
  obtain ⟨a, ha, _⟩ := Fin.exists_ne_and_ne_of_two_lt i i (by omega)
  obtain ⟨b, hbi, hba⟩ := Fin.exists_ne_and_ne_of_two_lt i a (by omega)
  have H := dist_triangle (terminalClipping hm x a) (terminalClipping hm x i)
    (terminalClipping hm x b)
  rw [clipping_star hm x hx (Ne.symm hba), clipping_star hm x hx ha,
    clipping_star hm x hx (Ne.symm hbi)] at H
  linarith

/-- A coordinate triangle excess is bounded by the full triangle excess. -/
theorem coordinate_excess_le (y : Fin m → L1 n) (i a b : Fin m) (j : Fin n) :
    |y i j - y a j| + |y i j - y b j| - |y a j - y b j| ≤
      dist (y i) (y a) + dist (y i) (y b) - dist (y a) (y b) := by
  simp_rw [l1_dist]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.single_le_sum (f := fun k : Fin n =>
    |y i k - y a k| + |y i k - y b k| - |y a k - y b k|)
  · intro k _
    have H := abs_sub_le (y a k) (y i k) (y b k)
    rw [abs_sub_comm (y a k) (y i k)] at H
    linarith
  · simp

theorem coordinate_to_end_le_radius (hx : UnitEquilateral x) (i : Fin m) (j : Fin n)
    {c : ℝ} (he : ∃ a b : Fin m, a ≠ b ∧ terminalClipping hm x a j = c ∧
      terminalClipping hm x b j = c) :
    |terminalClipping hm x i j - c| ≤ radius hm x i := by
  by_cases hi : terminalClipping hm x i j = c
  · rw [hi, sub_self, abs_zero]
    exact radius_nonneg hm x hx i
  obtain ⟨a, b, hab, ha, hb⟩ := he
  have hia : i ≠ a := by intro h; subst a; exact hi ha
  have hib : i ≠ b := by intro h; subst b; exact hi hb
  have H := coordinate_excess_le (terminalClipping hm x) i a b j
  rw [clipping_star hm x hx hia, clipping_star hm x hx hib,
    clipping_star hm x hx hab, ha, hb, sub_self, abs_zero] at H
  linarith

theorem coordinate_le_radius (hx : UnitEquilateral x) (i k : Fin m) (j : Fin n) :
    |terminalClipping hm x i j - terminalClipping hm x k j| ≤ radius hm x i := by
  have Hl := coordinate_to_end_le_radius hm x hx i j (clipped_low_twice hm (fun k => x k j))
  have Hu := coordinate_to_end_le_radius hm x hx i j (clipped_high_twice hm (fun k => x k j))
  have Hi := clipped_mem hm (fun k => x k j) i
  have Hk := clipped_mem hm (fun k => x k j) k
  rw [abs_le] at Hl Hu ⊢
  change _ ≤ _ ∧ _ ≤ _ at Hi Hk
  simp only [terminalClipping_apply] at Hl Hu ⊢
  constructor <;> linarith

/-- Part (4) of Proposition `prop:clipping`. -/
theorem clipping_coordinate_bound (hx : UnitEquilateral x) (i k : Fin m) (j : Fin n) :
    |terminalClipping hm x i j - terminalClipping hm x k j| ≤
      min (radius hm x i) (radius hm x k) := by
  apply le_min (coordinate_le_radius hm x hx i k j)
  rw [abs_sub_comm]
  exact coordinate_le_radius hm x hx k i j
end Family

/-- Part (3) of Proposition `prop:clipping`: the simultaneous removal of at
most two terminal labels per coordinate leaves a label untouched. -/
theorem clipping_untouched {n : ℕ} (hn : 2 ≤ n) (x : Fin (2 * n + 1) → L1 n) :
    ∃ p, terminalClipping (by omega) x p = x p ∧ radius (by omega) x p = 1 / 2 := by
  classical
  let ends : Fin n × Bool → Fin (2 * n + 1) := fun e =>
    order (fun k => x k e.1) (if e.2 then ⟨2 * n, by omega⟩ else ⟨0, by omega⟩)
  have H : ¬ Function.Surjective ends := by
    intro H
    have hc := Fintype.card_le_of_surjective ends H
    simp only [Fintype.card_fin, Fintype.card_prod, Fintype.card_bool] at hc
    omega
  unfold Function.Surjective at H
  push Not at H
  obtain ⟨p, hp⟩ := H
  have heq : terminalClipping (by omega) x p = x p := by
    apply PiLp.ext
    intro j
    change clipped (by omega) (fun k => x k j) p = x p j
    apply clipped_eq_of_not_terminal
    · intro H
      apply hp (j, false)
      simpa only [ends, Bool.false_eq_true, ↓reduceIte] using H.symm
    · intro H
      apply hp (j, true)
      simpa only [ends, ↓reduceIte, Nat.add_sub_cancel] using H.symm
  refine ⟨p, heq, ?_⟩
  simp [radius, displacement, heq]

/-- Part (5) of Proposition `prop:clipping`, including strict positivity. -/
theorem clipping_radius_bounds {n : ℕ} (hn : 2 ≤ n) {x : Fin (2 * n + 1) → L1 n}
    (hx : UnitEquilateral x) (i : Fin (2 * n + 1)) :
    1 / (2 * ((n : ℝ) - 1)) ≤ radius (by omega) x i ∧ radius (by omega) x i ≤ 1 / 2 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨?_, radius_le_half (by omega) x i⟩
  obtain ⟨p, _, hp⟩ := clipping_untouched hn x
  apply (div_le_iff₀ (by linarith : 0 < 2 * ((n : ℝ) - 1))).2
  by_cases hip : i = p
  · rw [hip, hp]
    linarith
  · have Hd := clipping_star (by omega) x hx hip
    rw [hp, l1_dist] at Hd
    have Hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
      (fun j _ => coordinate_le_radius (by omega) x hx i p j)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at Hsum
    rw [Hd] at Hsum
    nlinarith

theorem clipping_radius_pos {n : ℕ} (hn : 2 ≤ n) {x : Fin (2 * n + 1) → L1 n}
    (hx : UnitEquilateral x) (i : Fin (2 * n + 1)) : 0 < radius (by omega) x i := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < 2 * ((n : ℝ) - 1) := by linarith
  exact (one_div_pos.mpr hd).trans_le (clipping_radius_bounds hn hx i).1

end KusnerL1
