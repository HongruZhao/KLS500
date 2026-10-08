import KLS.WeightedDiffusionLiouville

/-!
# A coordinate energy-dual reduction for actual variance

Per-coordinate dual bounds on the derivatives control the actual diffusion
quadratic objective through integration by parts and Bochner. The variance
conclusion explicitly retains the unresolved diffusion-range density theorem.
The test f may be unbounded; C1 and genuine L2 membership are required.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Filter Set
open scoped BigOperators ContDiff Topology

noncomputable section
namespace KLS

variable {n : ℕ}

/-- A concrete energy-dual bound, expressed through actual compact C1 tests. -/
def CoordinateGradientDualBound (φ f : Space n → ℝ) (i : Fin n) (K : ℝ) : Prop :=
  ∀ h : Space n → ℝ, ContDiff ℝ 1 h → HasCompactSupport h →
    (∫ x, coordinateDerivative f i x * h x ∂potentialMeasure φ) ^ 2 ≤
      K * (∫ x, ‖gradient h x‖ ^ 2 ∂potentialMeasure φ)

lemma two_mul_le_add_of_sq_le_mul {a K B : ℝ}
    (hK : 0 ≤ K) (hB : 0 ≤ B) (h : a ^ 2 ≤ K * B) : 2 * a ≤ K + B := by
  have hsq : (2 * |a|) ^ 2 ≤ (K + B) ^ 2 := by
    rw [mul_pow, sq_abs]
    nlinarith [sq_nonneg (K - B)]
  have habs : 2 * |a| ≤ K + B :=
    (sq_le_sq₀ (by positivity) (add_nonneg hK hB)).mp hsq
  exact (mul_le_mul_of_nonneg_left (le_abs_self a) (by norm_num)).trans habs

/-- The H^-1-style estimate on the actual compact smooth diffusion range. -/
theorem gradient_dual_diffusion {φ f g : Space n → ℝ} {K : Fin n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hconv : ConvexOn ℝ univ φ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 3 g) (hc : HasCompactSupport g)
    (hK : ∀ i, 0 ≤ K i) (hdual : ∀ i, CoordinateGradientDualBound φ f i (K i)) :
    2 * (∫ x, f x * (-weightedDiffusion φ g x) ∂potentialMeasure φ) -
      (∫ x, (weightedDiffusion φ g x) ^ 2 ∂potentialMeasure φ) ≤ ∑ i, K i := by
  have hid := diffusionIntegrability_of_hasCompactSupport (hφ.of_le (by norm_num)) hf
    (hg.of_le (by norm_num)) hc
  have hbd := bochnerIntegrability_of_hasCompactSupport hφ hg hc
  have hcoord (i : Fin n) :
      2 * (∫ x, coordinateDerivative f i x * coordinateDerivative g i x ∂potentialMeasure φ) ≤
        K i + (∫ x, ‖gradient (coordinateDerivative g i) x‖ ^ 2 ∂potentialMeasure φ) := by
    apply two_mul_le_add_of_sq_le_mul (hK i) (integral_nonneg fun _ => sq_nonneg _)
    exact hdual i (coordinateDerivative g i)
      (contDiff_coordinateDerivative hg (m := 1) (by norm_num) i)
      (hasCompactSupport_coordinateDerivative hc i)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcoord i)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hs
  have hi : (∫ x, f x * (-weightedDiffusion φ g x) ∂potentialMeasure φ) =
      ∑ i : Fin n, ∫ x, coordinateDerivative f i x * coordinateDerivative g i x
        ∂potentialMeasure φ := by
    calc
      _ = -(∫ x, f x * weightedDiffusion φ g x ∂potentialMeasure φ) := by
        rw [← integral_neg]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = ∫ x, inner ℝ (gradient f x) (gradient g x) ∂potentialMeasure φ := by
        rw [integral_mul_weightedDiffusion_of_hasCompactSupport
          (hφ.of_le (by norm_num)) hf (hg.of_le (by norm_num)) hc]
        ring
      _ = _ := by
        simp_rw [← sum_coordinateDerivative_mul]
        exact integral_finsetSum Finset.univ (fun i _ => hid.deriv_mul_deriv i)
  have hh : (∑ i : Fin n, ∫ x, ‖gradient (coordinateDerivative g i) x‖ ^ 2
      ∂potentialMeasure φ) = ∫ x, hessianSquare g x ∂potentialMeasure φ := by
    rw [← integral_finsetSum Finset.univ
      (fun i _ => hbd.integrable_gradient_coordinateDerivative_sq i)]
    simp_rw [sum_norm_gradient_coordinateDerivative_sq]
  rw [← hi, hh] at hs
  have hb := integral_hessianSquare_le_diffusion_sq hφ hconv hg hc
  linarith

/-- The full variance passage for C1 L2 tests, conditional on genuine range density.
The per-coordinate premises are energy-dual bounds, not variance inequalities. -/
theorem variance_le_sum_gradient_dual_of_rangeDense {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] {K : Fin n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hconv : ConvexOn ℝ univ φ)
    (hf : ContDiff ℝ 1 f) (hf2 : MemLp f 2 (potentialMeasure φ))
    (hK : ∀ i, 0 ≤ K i) (hdual : ∀ i, CoordinateGradientDualBound φ f i (K i))
    (hdense : DiffusionRangeDense φ) :
    ProbabilityTheory.variance f (potentialMeasure φ) ≤ ∑ i, K i := by
  let F : Lp ℝ 2 (potentialMeasure φ) := hf2.toLp f
  have hF : (F : Space n → ℝ) =ᵐ[potentialMeasure φ] f := hf2.coeFn_toLp
  have hclosure : CenteredL2.center (potentialMeasure φ) F ∈
      closure (compactDiffusionRange φ : Set (Lp ℝ 2 (potentialMeasure φ))) :=
    hdense _ (CenteredL2.integral_center _ F)
  have hbound : ∀ v ∈ compactDiffusionRange φ,
      2 * inner ℝ F v - ‖v‖ ^ 2 ≤ ∑ i, K i := by
    rintro v ⟨g, hg, hc, hv⟩
    have hi : inner ℝ F v =
        ∫ x, f x * (-weightedDiffusion φ g x) ∂potentialMeasure φ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hF, hv] with x hx hy
      simp [hx, hy, RCLike.inner_apply, mul_comm]
    have hn : ‖v‖ ^ 2 =
        ∫ x, (weightedDiffusion φ g x) ^ 2 ∂potentialMeasure φ := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      simp [hx, RCLike.inner_apply, pow_two]
    rw [hi, hn]
    exact gradient_dual_diffusion hφ hconv hf hg hc hK hdual
  have he := CenteredL2.variance_le_of_center_mem_closure (potentialMeasure φ) hclosure hbound
  rwa [ProbabilityTheory.variance_congr hF] at he

end KLS
end

#print axioms KLS.gradient_dual_diffusion
#print axioms KLS.variance_le_sum_gradient_dual_of_rangeDense
