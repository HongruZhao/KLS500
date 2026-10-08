import KLS.DualTransportPairing

open MeasureTheory InnerProductSpace Matrix Set Filter Metric
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Only first derivatives of the actual potential occur in this weighted
transport remainder. The scalar bound t <= 1+t^2 uses the existing energy. -/
theorem weighted_transport_remainder_bound
    {u f ψ χ : Space n → ℝ} (hu : ContDiff ℝ 1 u) (hc : StrictConvexOn ℝ univ u)
    {C : ℝ≥0} (hψ : LipschitzWith C ψ) {c R δ ε M M₀ : ℝ}
    (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hM : 0 ≤ M) (hM₀ : 0 ≤ M₀)
    (hclose : ∀ x ∈ closedBall (0 : Space n) R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 c x| ≤ δ)
    (hψs : tsupport ψ ⊆ closedBall (0 : Space n) (R / 4))
    (hχone : ∀ x ∈ closedBall (0 : Space n) R, χ x = 1)
    (hdensity : ∀ x ∈ closedBall (0 : Space n) R, |f x - 1| ≤ ε ^ 2)
    (hbound : ∀ x ∈ closedBall (0 : Space n) R, |normalizedQuadraticError u 0 0 c ε x| ≤ M)
    (hψbound : ∀ x, |ψ x| ≤ M₀) (x : Space n) :
    |normalizedQuadraticError u 0 0 c ε x * (ψ x - f x * ψ (gradient u x))| ≤
      ε * M * ((C : ℝ) * χ x ^ 2 *
        ‖gradient (normalizedQuadraticError u 0 0 c ε) x‖ ^ 2 + ((C : ℝ) + M₀) * χ x ^ 2) := by
  let w := normalizedQuadraticError u 0 0 c ε
  have hcomp := tsupport_comp_gradient_subset_closedBall hu hc hR hδ hclose hψs
  by_cases hx : x ∈ closedBall (0 : Space n) R
  · rw [hχone x hx, one_pow, mul_one, mul_one]
    have hd : gradient u x - x = ε • gradient w x := by
      simpa only [sub_zero, zero_add] using
        gradient_sub_affine_eq_scaled_normalized_gradient hu 0 0 c hε.ne' x
    have hl := hψ.dist_le_mul (gradient u x) x
    rw [Real.dist_eq, dist_eq_norm, hd, norm_smul, Real.norm_eq_abs, abs_of_pos hε] at hl
    rw [abs_sub_comm] at hl
    have hf := mul_le_mul (hdensity x hx) (hψbound (gradient u x)) (abs_nonneg _) (sq_nonneg ε)
    rw [← abs_mul] at hf
    have hdiff : |ψ x - f x * ψ (gradient u x)| ≤
        (C : ℝ) * ε * ‖gradient w x‖ + ε ^ 2 * M₀ := calc
      _ = |(ψ x - ψ (gradient u x)) - (f x - 1) * ψ (gradient u x)| := by congr 1; ring
      _ ≤ |ψ x - ψ (gradient u x)| + |(f x - 1) * ψ (gradient u x)| := by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (ψ x - ψ (gradient u x)) (-((f x - 1) * ψ (gradient u x)))
      _ ≤ _ := by nlinarith [hl, hf]
    have hgrad : ‖gradient w x‖ ≤ ‖gradient w x‖ ^ 2 + 1 := by nlinarith [sq_nonneg (‖gradient w x‖-1)]
    have hεM₀ : ε * M₀ ≤ M₀ := mul_le_of_le_one_left hM₀ hε1
    have he : (C : ℝ) * ε * ‖gradient w x‖ + ε ^ 2 * M₀ ≤
        ε * ((C : ℝ) * ‖gradient w x‖ ^ 2 + ((C : ℝ) + M₀)) := by
      have hg := mul_le_mul_of_nonneg_left hgrad (mul_nonneg C.coe_nonneg hε.le)
      have hM0 := mul_le_mul_of_nonneg_left hεM₀ hε.le
      nlinarith
    rw [abs_mul]
    exact (mul_le_mul (hbound x hx) (hdiff.trans he) (abs_nonneg _) hM).trans_eq (by ring)
  · have hxψ : x ∉ tsupport ψ := by
      intro ht
      exact hx ((closedBall_subset_closedBall (by linarith : R / 4 ≤ R)) (hψs ht))
    have hxc : x ∉ tsupport (ψ ∘ gradient u) := fun ht => hx (hcomp ht)
    have hzcomp : ψ (gradient u x) = 0 := image_eq_zero_of_notMem_tsupport (f := ψ ∘ gradient u) hxc
    rw [hzcomp, image_eq_zero_of_notMem_tsupport hxψ]
    simp only [mul_zero, sub_zero, abs_zero]
    positivity

/-- Integrating the localized remainder gives a uniform O(epsilon) estimate
in terms of the genuine cutoff energy, without any second derivatives of u. -/
theorem abs_integral_weighted_transport_remainder_le
    {u f ψ χ : Space n → ℝ} (hu : ContDiff ℝ 1 u) (hc : StrictConvexOn ℝ univ u)
    {C : ℝ≥0} (hψ : LipschitzWith C ψ) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    {c R δ ε M M₀ : ℝ} (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hM : 0 ≤ M) (hM₀ : 0 ≤ M₀)
    (hclose : ∀ x ∈ closedBall (0 : Space n) R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 c x| ≤ δ)
    (hψs : tsupport ψ ⊆ closedBall (0 : Space n) (R / 4))
    (hχone : ∀ x ∈ closedBall (0 : Space n) R, χ x = 1)
    (hdensity : ∀ x ∈ closedBall (0 : Space n) R, |f x - 1| ≤ ε ^ 2)
    (hbound : ∀ x ∈ closedBall (0 : Space n) R, |normalizedQuadraticError u 0 0 c ε x| ≤ M)
    (hψbound : ∀ x, |ψ x| ≤ M₀) :
    |∫ x, normalizedQuadraticError u 0 0 c ε x * (ψ x - f x * ψ (gradient u x))| ≤
      ε * M * ((C : ℝ) * (∫ x, χ x ^ 2 *
        ‖gradient (normalizedQuadraticError u 0 0 c ε) x‖ ^ 2) +
          ((C : ℝ) + M₀) * (∫ x, χ x ^ 2)) := by
  let w := normalizedQuadraticError u 0 0 c ε
  have hgw := continuous_gradient_of_contDiff (contDiff_normalizedQuadraticError hu 0 0 c ε)
  have hχ2 : Integrable (fun x => χ x ^ 2) :=
    (hχ.pow 2).integrable_of_hasCompactSupport (by simpa [pow_two, Pi.mul_def] using hχc.mul_right)
  have hE : Integrable (fun x => χ x ^ 2 * ‖gradient w x‖ ^ 2) :=
    ((hχ.pow 2).mul (hgw.norm.pow 2)).integrable_of_hasCompactSupport
      (by simpa [pow_two, Pi.mul_def] using hχc.mul_right.mul_right)
  have hterm : Integrable (fun x => (C : ℝ) * χ x ^ 2 * ‖gradient w x‖ ^ 2) := by
    convert hE.const_mul (C : ℝ) using 1
    ext x
    ring
  have hH := (hterm.add (hχ2.const_mul ((C : ℝ) + M₀))).const_mul (ε * M)
  have hh := norm_integral_le_of_norm_le
    (f := fun x => w x * (ψ x - f x * ψ (gradient u x))) hH (Eventually.of_forall fun x =>
    weighted_transport_remainder_bound hu hc hψ hR hδ hε hε1 hM hM₀ hclose hψs
      hχone hdensity hbound hψbound x)
  change |∫ x, w x * (ψ x - f x * ψ (gradient u x))| ≤ _ at hh
  convert hh using 1
  simp only [Pi.add_apply]
  rw [integral_const_mul, integral_add hterm (hχ2.const_mul ((C : ℝ) + M₀))]
  simp_rw [mul_assoc, integral_const_mul]
  rfl

end KLS
end
