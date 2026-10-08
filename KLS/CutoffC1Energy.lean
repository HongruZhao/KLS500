import KLS.CompactC1L2Subsequence

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma integral_cutoff_mul_sq_le {χ w : Space n → ℝ}
    (hχ : Continuous χ) (hw : Continuous w) (hc : HasCompactSupport χ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x ∈ tsupport χ, |w x| ≤ M) :
    (∫ x, (χ x * w x) ^ 2) ≤ M ^ 2 * (∫ x, χ x ^ 2) := by
  rw [← integral_const_mul]
  apply integral_mono
  · exact ((hχ.mul hw).pow 2).integrable_of_hasCompactSupport
      (by simpa only [pow_two, Pi.mul_apply] using hc.mul_right.mul_right)
  · exact ((hχ.pow 2).integrable_of_hasCompactSupport
      (by simpa only [pow_two, Pi.mul_apply] using hc.mul_right)).const_mul _
  · intro x
    dsimp only
    by_cases hx : x ∈ tsupport χ
    · have hs : w x ^ 2 ≤ M ^ 2 := by nlinarith [hb x hx, sq_abs (w x), abs_nonneg (w x)]
      nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (χ x))]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp

lemma integral_cutoff_mul_coordinateDerivative_sq_le {χ w : Space n → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hw : ContDiff ℝ 1 w) (hc : HasCompactSupport χ)
    {M E : ℝ} (hM : 0 ≤ M) (hb : ∀ x ∈ tsupport χ, |w x| ≤ M)
    (he : (∫ x, ∑ i, χ x ^ 2 * coordinateDerivative w i x ^ 2) ≤ E) (i : Fin n) :
    (∫ x, coordinateDerivative (fun x => χ x * w x) i x ^ 2) ≤
      2 * E + 2 * M ^ 2 * (∫ x, ∑ j, coordinateDerivative χ j x ^ 2) := by
  have henergy (j : Fin n) : Integrable (fun x => χ x ^ 2 * coordinateDerivative w j x ^ 2) :=
    ((hχ.continuous.pow 2).mul
      ((contDiff_coordinateDerivative hw (m := 0) (by norm_num) j).continuous.pow 2)).integrable_of_hasCompactSupport
      (by simpa only [pow_two, Pi.mul_apply] using hc.mul_right.mul_right)
  have hcut (j : Fin n) : Integrable (fun x => coordinateDerivative χ j x ^ 2) :=
    ((contDiff_coordinateDerivative hχ (m := 0) (by norm_num) j).continuous.pow 2).integrable_of_hasCompactSupport
      (by simpa only [pow_two, Pi.mul_apply] using (hasCompactSupport_coordinateDerivative hc j).mul_right)
  have hprod : HasCompactSupport (fun x => χ x * w x) := hc.mul_right
  have hi : Integrable (fun x => coordinateDerivative (fun x => χ x * w x) i x ^ 2) :=
    ((contDiff_coordinateDerivative (hχ.mul hw) (m := 0) (by norm_num) i).continuous.pow 2).integrable_of_hasCompactSupport
      (by simpa only [pow_two, Pi.mul_apply] using (hasCompactSupport_coordinateDerivative hprod i).mul_right)
  have hsumE := integrable_finsetSum (s := Finset.univ) (fun j _ => henergy j)
  have hsumχ := integrable_finsetSum (s := Finset.univ) (fun j _ => hcut j)
  have hpoint (x : Space n) : coordinateDerivative (fun x => χ x * w x) i x ^ 2 ≤
      2 * (∑ j, χ x ^ 2 * coordinateDerivative w j x ^ 2) +
        2 * M ^ 2 * (∑ j, coordinateDerivative χ j x ^ 2) := by
    rw [coordinateDerivative_mul (hχ.differentiable (by norm_num) x) (hw.differentiable (by norm_num) x)]
    have hE : χ x ^ 2 * coordinateDerivative w i x ^ 2 ≤
        ∑ j, χ x ^ 2 * coordinateDerivative w j x ^ 2 :=
      Finset.single_le_sum (f := fun j => χ x ^ 2 * coordinateDerivative w j x ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ i)
    have hχi : coordinateDerivative χ i x ^ 2 ≤ ∑ j, coordinateDerivative χ j x ^ 2 :=
      Finset.single_le_sum (f := fun j => coordinateDerivative χ j x ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    have hwχ : w x ^ 2 * coordinateDerivative χ i x ^ 2 ≤
        M ^ 2 * coordinateDerivative χ i x ^ 2 := by
      by_cases hx : x ∈ tsupport χ
      · have hs : w x ^ 2 ≤ M ^ 2 := by nlinarith [hb x hx, sq_abs (w x), abs_nonneg (w x)]
        exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
      · have hz : coordinateDerivative χ i x = 0 := image_eq_zero_of_notMem_tsupport
          (fun ht => hx (tsupport_coordinateDerivative_subset χ i ht))
        simp [hz]
    have hh := mul_le_mul_of_nonneg_left hχi (sq_nonneg M)
    nlinarith [sq_nonneg (χ x * coordinateDerivative w i x - w x * coordinateDerivative χ i x)]
  have hbnd := integral_mono hi ((hsumE.const_mul 2).add (hsumχ.const_mul (2 * M ^ 2))) hpoint
  change (∫ x, coordinateDerivative (fun x => χ x * w x) i x ^ 2) ≤
    ∫ x, 2 * (∑ j, χ x ^ 2 * coordinateDerivative w j x ^ 2) +
      2 * M ^ 2 * (∑ j, coordinateDerivative χ j x ^ 2) at hbnd
  rw [integral_add (hsumE.const_mul 2) (hsumχ.const_mul (2 * M ^ 2)),
    integral_const_mul, integral_const_mul] at hbnd
  linarith

/-- A uniform cutoff energy bound for bounded C1 functions gives a genuine
strong L2 convergent subsequence of their actual compact localizations. -/
theorem exists_strong_L2_subsequence_of_cutoff_energy
    {w : ℕ → Space n → ℝ} {χ : Space n → ℝ}
    (hw : ∀ k, ContDiff ℝ 1 (w k)) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    {R M E : ℝ} (hM : 0 ≤ M) (hE : 0 ≤ E) (hs : tsupport χ ⊆ closedBall (0 : Space n) R)
    (hb : ∀ k x, x ∈ tsupport χ → |w k x| ≤ M)
    (he : ∀ k, (∫ x, ∑ i, χ x ^ 2 * coordinateDerivative (w k) i x ^ 2) ≤ E) :
    ∃ (g : Lp ℝ 2 (volume : Measure (Space n))) (σ : ℕ → ℕ), StrictMono σ ∧
      Tendsto (fun k => eLpNorm ((fun x => χ x * w (σ k) x) - (g : Space n → ℝ)) 2 volume) atTop (𝓝 0) := by
  apply exists_strong_L2_subsequence_of_compact_C1_bounds (fun k => hχ.mul (hw k))
    (A := M ^ 2 * (∫ x, χ x ^ 2))
    (B := 2 * E + 2 * M ^ 2 * (∫ x, ∑ j, coordinateDerivative χ j x ^ 2))
  · exact mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => sq_nonneg _))
  · exact add_nonneg (mul_nonneg (by norm_num) hE)
      (mul_nonneg (by positivity) (integral_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))))
  · intro k
    exact tsupport_mul_subset_left.trans hs
  · intro k
    exact integral_cutoff_mul_sq_le hχ.continuous (hw k).continuous hc hM (hb k)
  · intro k i
    exact integral_cutoff_mul_coordinateDerivative_sq_le hχ (hw k) hc hM (hb k) (he k) i

end KLS
end
