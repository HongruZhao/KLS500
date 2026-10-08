import KLS.FirstOrderCoordinateTaylor

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma abs_integral_pairing_le_of_transport_remainder
    {a b f g H : Space n → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hfa : Integrable (fun x => f x * a x)) (hb : Integrable b) (hg : Integrable g)
    (hH : Integrable H) (htransport : (∫ x, f x * a x) = ∫ x, b x)
    (hrem : ∀ x, |f x * a x - b x - ε * g x| ≤ ε ^ 2 * H x) :
    |∫ x, g x| ≤ ε * (∫ x, H x) := by
  have he : (∫ x, f x * a x - b x - ε * g x) = -(ε * (∫ x, g x)) := by
    rw [integral_sub (f := fun x => f x * a x - b x) (g := fun x => ε * g x)
      (hfa.sub hb) (hg.const_mul ε), integral_sub hfa hb,
      integral_const_mul, htransport]
    ring
  have ht := norm_integral_le_of_norm_le (f := fun x => f x * a x - b x - ε * g x)
    (hH.const_mul (ε ^ 2)) (Eventually.of_forall fun x => hrem x)
  change |∫ x, f x * a x - b x - ε * g x| ≤ ∫ x, ε ^ 2 * H x at ht
  rw [he, abs_neg, abs_mul, abs_of_pos hε, integral_const_mul] at ht
  apply (mul_le_mul_iff_right₀ hε).mp
  nlinarith [ht]

lemma gradient_eq_zero_of_notMem_tsupport {ψ : Space n → ℝ} {x : Space n}
    (hx : x ∉ tsupport ψ) : gradient ψ x = 0 := by
  ext i
  rw [← coordinateDerivative_eq_gradient]
  exact image_eq_zero_of_notMem_tsupport (fun ht => hx (tsupport_coordinateDerivative_subset ψ i ht))

/-- The first-order transport remainder is dominated by epsilon squared
times the actual local energy density and a compact density-error term. -/
theorem first_order_transport_remainder_bound
    {u f ψ χ : Space n → ℝ} (hu : ContDiff ℝ 1 u) (hc : StrictConvexOn ℝ univ u)
    (hψ : ContDiff ℝ 2 ψ) {c R δ ε M₀ M₂ : ℝ}
    (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16) (hε : 0 < ε) (hM₀ : 0 ≤ M₀) (hM₂ : 0 ≤ M₂)
    (hclose : ∀ x ∈ closedBall (0 : Space n) R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 c x| ≤ δ)
    (hψs : tsupport ψ ⊆ closedBall (0 : Space n) (R / 4))
    (hχone : ∀ x ∈ closedBall (0 : Space n) R, χ x = 1)
    (hdensity : ∀ x ∈ closedBall (0 : Space n) R, |f x - 1| ≤ ε ^ 2)
    (hψbound : ∀ x, |ψ x| ≤ M₀)
    (hHbound : ∀ x, ∀ i j, |coordinateHessian ψ x i j| ≤ M₂) (x : Space n) :
    |f x * ψ (gradient u x) - ψ x -
      ε * inner ℝ (gradient ψ x) (gradient (normalizedQuadraticError u 0 0 c ε) x)| ≤
      ε ^ 2 * ((n : ℝ) ^ 2 * M₂ * χ x ^ 2 *
        ‖gradient (normalizedQuadraticError u 0 0 c ε) x‖ ^ 2 + M₀ * χ x ^ 2) := by
  let w := normalizedQuadraticError u 0 0 c ε
  have hcomp := tsupport_comp_gradient_subset_closedBall hu hc hR hδ hclose hψs
  by_cases hx : x ∈ closedBall (0 : Space n) R
  · rw [hχone x hx, one_pow, mul_one, mul_one]
    have hd : gradient u x - x = ε • gradient w x := by
      simpa only [sub_zero, zero_add] using
        gradient_sub_affine_eq_scaled_normalized_gradient hu 0 0 c hε.ne' x
    have ht := abs_first_order_taylor_remainder_le hψ hM₂ hHbound x (gradient u x)
    rw [hd, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hε, mul_pow] at ht
    have hf := mul_le_mul (hdensity x hx) (hψbound (gradient u x)) (abs_nonneg _) (sq_nonneg ε)
    rw [← abs_mul] at hf
    calc
      _ = |(ψ (gradient u x) - ψ x - ε * inner ℝ (gradient ψ x) (gradient w x)) +
          (f x - 1) * ψ (gradient u x)| := by congr 1; ring
      _ ≤ |ψ (gradient u x) - ψ x - ε * inner ℝ (gradient ψ x) (gradient w x)| +
          |(f x - 1) * ψ (gradient u x)| := abs_add_le _ _
      _ ≤ _ := by nlinarith [ht, hf]
  · have hxψ : x ∉ tsupport ψ := by
      intro ht
      exact hx ((closedBall_subset_closedBall (by linarith : R / 4 ≤ R)) (hψs ht))
    have hxc : x ∉ tsupport (ψ ∘ gradient u) := fun ht => hx (hcomp ht)
    have hzcomp : ψ (gradient u x) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := ψ ∘ gradient u) hxc
    rw [hzcomp, image_eq_zero_of_notMem_tsupport hxψ, gradient_eq_zero_of_notMem_tsupport hxψ]
    simp only [mul_zero, sub_zero, inner_zero_left, abs_zero]
    positivity

/-- The actual transport identity now forces the weak harmonic test pairing
to be O(epsilon), with an explicit coefficient involving local energy. -/
theorem abs_integral_gradient_pairing_le_of_localized_transport
    {u f ψ χ : Space n → ℝ} (hu : ContDiff ℝ 1 u) (hc : StrictConvexOn ℝ univ u)
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) {c R δ ε M₀ M₂ : ℝ}
    (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16) (hε : 0 < ε) (hM₀ : 0 ≤ M₀) (hM₂ : 0 ≤ M₂)
    (hclose : ∀ x ∈ closedBall (0 : Space n) R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 c x| ≤ δ)
    (hψs : tsupport ψ ⊆ closedBall (0 : Space n) (R / 4))
    (hχone : ∀ x ∈ closedBall (0 : Space n) R, χ x = 1)
    (hdensity : ∀ x ∈ closedBall (0 : Space n) R, |f x - 1| ≤ ε ^ 2)
    (hψbound : ∀ x, |ψ x| ≤ M₀)
    (hHbound : ∀ x, ∀ i j, |coordinateHessian ψ x i j| ≤ M₂)
    (hint : Integrable (fun x => f x * ψ (gradient u x)))
    (htransport : (∫ x, f x * ψ (gradient u x)) = ∫ x, ψ x) :
    |∫ x, inner ℝ (gradient ψ x) (gradient (normalizedQuadraticError u 0 0 c ε) x)| ≤
      ε * ((n : ℝ) ^ 2 * M₂ * (∫ x, χ x ^ 2 *
        ‖gradient (normalizedQuadraticError u 0 0 c ε) x‖ ^ 2) + M₀ * (∫ x, χ x ^ 2)) := by
  let w := normalizedQuadraticError u 0 0 c ε
  have hw : ContDiff ℝ 1 w := contDiff_normalizedQuadraticError hu _ _ _ _
  have hgw := continuous_gradient_of_contDiff hw
  have hgψ := continuous_gradient_of_contDiff (hψ.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2))
  have hg : Integrable (fun x => inner ℝ (gradient ψ x) (gradient w x)) :=
    (hgψ.inner hgw).integrable_of_hasCompactSupport (hψc.of_isClosed_subset
      (isClosed_tsupport _) (closure_minimal (fun x hx => by
        by_contra hnot
        exact hx (by simp [gradient_eq_zero_of_notMem_tsupport hnot])) (isClosed_tsupport ψ)))
  have hχ2 : Integrable (fun x => χ x ^ 2) :=
    (hχ.pow 2).integrable_of_hasCompactSupport (by simpa [pow_two, Pi.mul_def] using hχc.mul_right)
  have henergy : Integrable (fun x => χ x ^ 2 * ‖gradient w x‖ ^ 2) :=
    ((hχ.pow 2).mul (hgw.norm.pow 2)).integrable_of_hasCompactSupport
      (by simpa [pow_two, Pi.mul_def] using hχc.mul_right.mul_right)
  have hterm : Integrable (fun x => (n : ℝ) ^ 2 * M₂ * χ x ^ 2 * ‖gradient w x‖ ^ 2) := by
    convert henergy.const_mul ((n : ℝ) ^ 2 * M₂) using 1
    ext x
    ring
  have hH : Integrable (fun x => (n : ℝ) ^ 2 * M₂ * χ x ^ 2 * ‖gradient w x‖ ^ 2 + M₀ * χ x ^ 2) :=
    hterm.add (hχ2.const_mul M₀)
  have hh := abs_integral_pairing_le_of_transport_remainder hε hint
    (hψ.continuous.integrable_of_hasCompactSupport hψc) hg hH htransport
    (first_order_transport_remainder_bound hu hc hψ hR hδ hε hM₀ hM₂ hclose hψs hχone hdensity hψbound hHbound)
  convert hh using 1
  rw [integral_add hterm (hχ2.const_mul M₀)]
  simp_rw [mul_assoc, integral_const_mul]
  rfl

end KLS
end
