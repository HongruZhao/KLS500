import KLS.RelativeMomentDensity

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal ENNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma exists_small_holder_radius {R C α ε : ℝ}
    (hR : 0 < R) (hC : 0 < C) (hα : 0 < α) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ C * r ^ α ≤ ε ^ 2 := by
  let t : ℝ := (ε ^ 2 / C) ^ α⁻¹
  have hb : 0 < ε ^ 2 / C := div_pos (sq_pos_of_pos hε) hC
  have ht : 0 < t := Real.rpow_pos_of_pos hb _
  let r : ℝ := min R t
  have hr : 0 < r := lt_min hR ht
  refine ⟨r, hr, min_le_left _ _, ?_⟩
  have hh := Real.rpow_le_rpow hr.le (min_le_right R t) hα.le
  have htα : t ^ α = ε ^ 2 / C := Real.rpow_inv_rpow hb.le hα.ne'
  rw [htα] at hh
  have hm := mul_le_mul_of_nonneg_left hh hC.le
  exact hm.trans_eq (by field_simp)

/-- A compatible geometric flatness rate is chosen from the actual spatial
contraction and Hölder exponent. It also accommodates an existing one-step
improvement factor theta by allowing a weaker, still strict, contraction. -/
theorem exists_compatible_density_flatness_rate {ρ α θ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hα : 0 < α) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ θ ≤ η ∧ ρ ^ α ≤ η ^ 2 := by
  let η : ℝ := max θ (Real.sqrt (ρ ^ α))
  have hp : 0 ≤ ρ ^ α := Real.rpow_nonneg hρ.le α
  have hpow : ρ ^ α < 1 := Real.rpow_lt_one hρ.le hρ1 hα
  have hsqrt : Real.sqrt (ρ ^ α) < 1 := by
    have hh := Real.sq_sqrt hp
    have hn := Real.sqrt_nonneg (ρ ^ α)
    nlinarith
  refine ⟨η, hθ.trans_le (le_max_left _ _), max_lt hθ1 hsqrt, le_max_left _ _, ?_⟩
  have hmax : Real.sqrt (ρ ^ α) ≤ η := le_max_right _ _
  have hη : 0 ≤ η := (Real.sqrt_nonneg _).trans hmax
  nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg (ρ ^ α)]

/-- Once initial density size and the contraction rates are compatible,
the actual Hölder density error is bounded by the square of every subsequent
flatness scale. The maps E need only satisfy the proved spatial-radius bound. -/
theorem relative_density_le_geometric_flatness_sq
    {f : Space n → ℝ} {c : Space n} {R C α r ρ η ε : ℝ}
    (hC : 0 ≤ C) (hα : 0 ≤ α) (hr : 0 ≤ r) (hrR : r ≤ R)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hcompatible : ρ ^ α ≤ η ^ 2) (hsmall : C * r ^ α ≤ ε ^ 2)
    (hholder : ∀ x ∈ closedBall c R, |f x / f c - 1| ≤ C * ‖x - c‖ ^ α)
    {E : ℕ → Space n → Space n} {S : Set (Space n)}
    (hmap : ∀ j, ∀ y ∈ S, ‖E j y - c‖ ≤ r * ρ ^ j) :
    ∀ j, ∀ y ∈ S, |f (E j y) / f c - 1| ≤ (ε * η ^ j) ^ 2 := by
  intro j y hy
  have hnorm := hmap j y hy
  have hrhoj : ρ ^ j ≤ 1 := pow_le_one₀ hρ hρ1
  have hmem : E j y ∈ closedBall c R := by
    change ‖E j y - c‖ ≤ R
    exact hnorm.trans ((mul_le_mul_of_nonneg_left hrhoj hr).trans (by simpa using hrR))
  have hpower : ‖E j y - c‖ ^ α ≤ (r * ρ ^ j) ^ α :=
    Real.rpow_le_rpow (norm_nonneg _) hnorm hα
  have hpowcompat : (ρ ^ α) ^ j ≤ (η ^ 2) ^ j :=
    pow_le_pow_left₀ (Real.rpow_nonneg hρ α) hcompatible j
  calc
    _ ≤ C * ‖E j y - c‖ ^ α := hholder _ hmem
    _ ≤ C * (r * ρ ^ j) ^ α := mul_le_mul_of_nonneg_left hpower hC
    _ = (C * r ^ α) * (ρ ^ α) ^ j := by
      rw [Real.mul_rpow hr (pow_nonneg hρ j), ← Real.rpow_pow_comm hρ]
      ring
    _ ≤ (ε ^ 2) * (η ^ 2) ^ j :=
      mul_le_mul hsmall hpowcompat (pow_nonneg (Real.rpow_nonneg hρ α) j) (sq_nonneg ε)
    _ = (ε * η ^ j) ^ 2 := by rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm 2 j]

end KLS
end
