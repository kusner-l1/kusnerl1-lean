import KusnerL1.Metric

/-! Pairwise forms of the energy identities in Section 3. Ordered pairs are
used with a factor of two; diagonal contributions vanish. -/
namespace KusnerL1
open scoped BigOperators
open Finset

section Star
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
variable (y : ι → L1 n) (r : ι → ℝ)

noncomputable def mass (i : ι) : ℝ := (r i)⁻¹
noncomputable def totalMass : ℝ := ∑ i, mass r i
noncomputable def pairEnergy (j : Fin n) : ℝ :=
  (∑ i, ∑ k, mass r i * mass r k * |y i j - y k j|) / (2 * totalMass r)

def Star : Prop := ∀ i k, i ≠ k → dist (y i) (y k) = r i + r k

omit [DecidableEq ι] in
theorem totalMass_pos [Nonempty ι] (hr : ∀ i, 0 < r i) : 0 < totalMass r := by
  apply sum_pos
  · intro i _
    exact inv_pos.mpr (hr i)
  · exact univ_nonempty

omit [Fintype ι] in
theorem weighted_distance (hr : ∀ i, 0 < r i) (hs : Star y r) (i k : ι) :
    mass r i * mass r k * dist (y i) (y k) =
      mass r i + mass r k - (if i = k then 2 * mass r i else 0) := by
  by_cases hik : i = k
  · subst k
    simp
    ring
  · rw [if_neg hik, hs i k hik]
    unfold mass
    field_simp [(hr i).ne', (hr k).ne']
    ring

/-- Pairwise form of Proposition `prop:total-energy`. -/
theorem total_pairEnergy [Nonempty ι] (hr : ∀ i, 0 < r i) (hs : Star y r) :
    ∑ j, pairEnergy y r j = Fintype.card ι - 1 := by
  have ht := totalMass_pos r hr
  have H : (∑ i, ∑ k, mass r i * mass r k * dist (y i) (y k)) =
      2 * ((Fintype.card ι : ℝ) - 1) * totalMass r := by
    simp_rw [weighted_distance y r hr hs]
    simp [sum_add_distrib, sum_sub_distrib, ← mul_sum, totalMass]
    ring
  simp only [pairEnergy, ← sum_div]
  rw [sum_comm]
  conv_lhs => arg 1; arg 2; ext i; rw [sum_comm]
  simp_rw [← mul_sum, ← l1_dist]
  rw [H]
  field_simp

/-- The signed pairwise calculation in Lemma `lem:weighted-quadratic`. -/
theorem weighted_pair_quadratic (hr : ∀ i, 0 < r i) (hs : Star y r)
    (f : ι → ℝ) (hf : ∑ i, mass r i * f i = 0) :
    (∑ i, ∑ k, mass r i * mass r k * f i * f k * dist (y i) (y k)) =
      -2 * ∑ i, mass r i * f i ^ 2 := by
  have hp (i k : ι) : mass r i * mass r k * f i * f k * dist (y i) (y k) =
      f i * (mass r k * f k) + (mass r i * f i) * f k -
        (if i = k then 2 * mass r i * f i ^ 2 else 0) := by
    have H := weighted_distance y r hr hs i k
    by_cases hik : i = k
    · subst k
      simp
      ring
    · rw [if_neg hik] at H ⊢
      calc
        _ = (mass r i * mass r k * dist (y i) (y k)) * (f i * f k) := by ring
        _ = _ := by rw [H]; ring

  simp_rw [hp, sum_sub_distrib, sum_add_distrib]
  simp only [← mul_sum, ← sum_mul, hf, mul_zero, zero_mul,
    sum_ite_eq, mem_univ, if_true, sum_const_zero]
  simp only [mul_assoc, ← mul_sum]
  ring
end Star

/-- A cut separates exactly those labels with unequal indicators. -/
noncomputable def cutDistance {ι : Type*} [DecidableEq ι] (C : Finset ι) (i k : ι) : ℝ :=
  |(if i ∈ C then (1 : ℝ) else 0) - (if k ∈ C then (1 : ℝ) else 0)|

theorem cutDistance_polynomial {ι : Type*} [DecidableEq ι] (C : Finset ι) (i k : ι) :
    cutDistance C i k = (if i ∈ C then (1 : ℝ) else 0) + (if k ∈ C then (1 : ℝ) else 0) -
      2 * (if i ∈ C then (1 : ℝ) else 0) * (if k ∈ C then (1 : ℝ) else 0) := by
  unfold cutDistance
  split_ifs <;> norm_num

/-- The total weight of the ordered pairs separated by a cut. -/
theorem cut_pair_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Finset ι) (v : ι → ℝ) :
    (∑ i, ∑ k, v i * v k * cutDistance C i k) =
      2 * (∑ i ∈ C, v i) * ((∑ i, v i) - ∑ i ∈ C, v i) := by
  simp_rw [cutDistance_polynomial]
  have H (i k : ι) : v i * v k *
      ((if i ∈ C then (1 : ℝ) else 0) + (if k ∈ C then (1 : ℝ) else 0) -
      2 * (if i ∈ C then (1 : ℝ) else 0) * (if k ∈ C then (1 : ℝ) else 0)) =
      (if i ∈ C then v i else 0) * v k + v i * (if k ∈ C then v k else 0) -
        2 * (if i ∈ C then v i else 0) * (if k ∈ C then v k else 0) := by
    split_ifs <;> ring
  simp_rw [H, sum_sub_distrib, sum_add_distrib, ← mul_sum, ← sum_mul]
  simp only [sum_ite_mem, univ_inter, ← mul_sum]
  ring

/-- The zero-mean specialization used in the weighted quadratic identity. -/
theorem cut_pair_sum_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Finset ι) (v : ι → ℝ) (hv : ∑ i, v i = 0) :
    (∑ i, ∑ k, v i * v k * cutDistance C i k) = -2 * (∑ i ∈ C, v i) ^ 2 := by
  rw [cut_pair_sum, hv]
  ring

end KusnerL1
