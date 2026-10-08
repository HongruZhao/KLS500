import KLS.SublevelCutoffProfile
import KLS.ConvexPotentialCoercivity

/-!
# Actual cutoffs on compact sublevels of the potential

The cutoff and auxiliary function are explicitly composed with the actual
potential height. Their compact support follows from the proved coercivity
of a finite convex potential; no inverse-Hessian growth bound is assumed.
-/

open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS

variable {n : ℕ}

lemma contDiff_potentialHeight {φ : Space n → ℝ} {k : ℕ∞ω}
    (hφ : ContDiff ℝ k φ) (x₀ : Space n) : ContDiff ℝ k (potentialHeight φ x₀) :=
  (hφ.sub contDiff_const).add contDiff_const

lemma potentialHeight_ge_one {φ : Space n → ℝ} {x₀ : Space n}
    (hmin : ∀ x, φ x₀ ≤ φ x) (x : Space n) : 1 ≤ potentialHeight φ x₀ x := by
  unfold potentialHeight
  linarith [hmin x]

lemma hasCompactSupport_comp_potentialHeight {φ : Space n → ℝ}
    (hφ : Continuous φ) (hconv : ConvexOn ℝ univ φ)
    [IsFiniteMeasure (potentialMeasure φ)] (x₀ : Space n)
    {q : ℝ → ℝ} {A c : ℝ} (hc : 0 < c) (hq : ∀ t, A ≤ t → q t = 0) :
    HasCompactSupport (fun x => q (c * potentialHeight φ x₀ x)) := by
  apply (isCompact_sublevel_of_finite_potentialMeasure hφ hconv (A / c + φ x₀ - 1)).of_isClosed_subset
    (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_le hφ continuous_const)
  intro x hx
  have hlt : c * potentialHeight φ x₀ x < A := by
    apply lt_of_not_ge
    intro hge
    exact hx (hq _ hge)
  have hdiv : potentialHeight φ x₀ x < A / c := (lt_div_iff₀ hc).mpr (by nlinarith)
  dsimp [potentialHeight] at hdiv ⊢
  linarith

def potentialSublevelCutoff (φ : Space n → ℝ) (x₀ : Space n) (c : ℝ) (x : Space n) : ℝ :=
  scaledSublevelProfile c (potentialHeight φ x₀ x)

def potentialSublevelTail (φ : Space n → ℝ) (x₀ : Space n) (c : ℝ) (x : Space n) : ℝ :=
  scaledSublevelTail c (potentialHeight φ x₀ x)

lemma potentialSublevelCutoff_contDiff {φ : Space n → ℝ} (hφ : ContDiff ℝ 4 φ)
    (x₀ : Space n) (c : ℝ) : ContDiff ℝ 2 (potentialSublevelCutoff φ x₀ c) :=
  ((scaledSublevelProfile_contDiff c).of_le (by simp)).comp
    (contDiff_potentialHeight (hφ.of_le (by norm_num)) x₀)

lemma potentialSublevelTail_contDiff {φ : Space n → ℝ} (hφ : ContDiff ℝ 4 φ)
    (x₀ : Space n) (c : ℝ) : ContDiff ℝ 1 (potentialSublevelTail φ x₀ c) :=
  (scaledSublevelTail_contDiff c).comp (contDiff_potentialHeight (hφ.of_le (by norm_num)) x₀)

lemma potentialSublevelCutoff_hasCompactSupport {φ : Space n → ℝ}
    (hφ : Continuous φ) (hconv : ConvexOn ℝ univ φ)
    [IsFiniteMeasure (potentialMeasure φ)] (x₀ : Space n) {c : ℝ} (hc : 0 < c) :
    HasCompactSupport (potentialSublevelCutoff φ x₀ c) :=
  hasCompactSupport_comp_potentialHeight hφ hconv x₀ hc
    (fun _ ht => sublevelCutoffProfile_zero ht)

lemma potentialSublevelTail_hasCompactSupport {φ : Space n → ℝ}
    (hφ : Continuous φ) (hconv : ConvexOn ℝ univ φ)
    [IsFiniteMeasure (potentialMeasure φ)] (x₀ : Space n) {c : ℝ} (hc : 0 < c) :
    HasCompactSupport (potentialSublevelTail φ x₀ c) := by
  have h := hasCompactSupport_comp_potentialHeight hφ hconv x₀ hc
    (fun t ht => sublevelCutoffTail_zero ht)
  exact h.mul_left

lemma potentialSublevelCutoff_mem_Icc (φ : Space n → ℝ) (x₀ x : Space n) (c : ℝ) :
    potentialSublevelCutoff φ x₀ c x ∈ Icc (0 : ℝ) 1 :=
  ⟨sublevelCutoffProfile_nonneg _, sublevelCutoffProfile_le_one _⟩

lemma potentialSublevelCutoff_tendsto_one (φ : Space n → ℝ) (x₀ x : Space n) :
    Tendsto (fun c : ℝ => potentialSublevelCutoff φ x₀ c x) (𝓝 0) (𝓝 1) := by
  have h := sublevelCutoffProfile_contDiff.continuous.continuousAt.tendsto.comp
    ((tendsto_id : Tendsto (fun c : ℝ => c) (𝓝 0) (𝓝 0)).mul_const (potentialHeight φ x₀ x))
  simpa only [zero_mul, sublevelCutoffProfile_one (by norm_num : (0 : ℝ) ≤ 1),
    Function.comp_def, id_eq, potentialSublevelCutoff, scaledSublevelProfile] using h

lemma coordinateDerivative_potentialSublevelTail {φ : Space n → ℝ} (hφ : ContDiff ℝ 4 φ)
    (x₀ x : Space n) (c : ℝ) (i : Fin n) :
    coordinateDerivative (potentialSublevelTail φ x₀ c) i x =
      -(c ^ 2 * ‖deriv (deriv sublevelCutoffProfile) (c * potentialHeight φ x₀ x)‖) *
        coordinateDerivative (potentialHeight φ x₀) i x := by
  change coordinateDerivative (fun y => scaledSublevelTail c (potentialHeight φ x₀ y)) i x = _
  rw [coordinateDerivative_scalar_comp
    ((scaledSublevelTail_contDiff c).differentiable (by norm_num) _)
    ((contDiff_potentialHeight hφ x₀).differentiable (by norm_num) _), scaledSublevelTail_deriv]

/-- The actual cutoff diffusion has precisely the two terms used in A.4. -/
theorem hessianMetricDiffusion_potentialSublevelCutoff {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (V : Space n → ℝ) (x₀ x : Space n) (c : ℝ) :
    hessianMetricDiffusion φ V (potentialSublevelCutoff φ x₀ c) x =
      c * deriv sublevelCutoffProfile (c * potentialHeight φ x₀ x) *
        hessianMetricDiffusion φ V (potentialHeight φ x₀) x +
      c ^ 2 * deriv (deriv sublevelCutoffProfile) (c * potentialHeight φ x₀ x) *
        inverseHessianGradientForm φ (potentialHeight φ x₀) x := by
  change hessianMetricDiffusion φ V (fun y => scaledSublevelProfile c (potentialHeight φ x₀ y)) x = _
  rw [hessianMetricDiffusion_scalar_comp φ V
    ((scaledSublevelProfile_contDiff c).of_le (by simp))
    (contDiff_potentialHeight (hφ.of_le (by norm_num)) x₀),
    scaledSublevelProfile_deriv, scaledSublevelProfile_second]

/-- The potentially unbounded inverse-Hessian contribution is an actual
integrable function, identified through the compact auxiliary test. -/
theorem potentialSublevelTail_energy_identity {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hconv : ConvexOn ℝ univ φ) [IsFiniteMeasure (potentialMeasure φ)]
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (x₀ : Space n) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x => c ^ 2 * ‖deriv (deriv sublevelCutoffProfile) (c * potentialHeight φ x₀ x)‖ *
      inverseHessianGradientForm φ (potentialHeight φ x₀) x) (potentialMeasure φ) ∧
    (∫ x, c ^ 2 * ‖deriv (deriv sublevelCutoffProfile) (c * potentialHeight φ x₀ x)‖ *
      inverseHessianGradientForm φ (potentialHeight φ x₀) x ∂potentialMeasure φ) =
    ∫ x, potentialSublevelTail φ x₀ c x * hessianMetricDiffusion φ V (potentialHeight φ x₀) x
      ∂potentialMeasure φ := by
  have hf := potentialSublevelTail_contDiff hφ x₀ c
  have hg : ContDiff ℝ 2 (potentialHeight φ x₀) :=
    contDiff_potentialHeight (hφ.of_le (by norm_num)) x₀
  have hfc := potentialSublevelTail_hasCompactSupport hφ.continuous hconv x₀ hc
  have heq (x : Space n) :
      (∑ i, ∑ j, (coordinateHessian φ x)⁻¹ i j * coordinateDerivative (potentialSublevelTail φ x₀ c) i x *
        coordinateDerivative (potentialHeight φ x₀) j x) =
      -(c ^ 2 * ‖deriv (deriv sublevelCutoffProfile) (c * potentialHeight φ x₀ x)‖ *
        inverseHessianGradientForm φ (potentialHeight φ x₀) x) := by
    simp_rw [coordinateDerivative_potentialSublevelTail hφ]
    unfold inverseHessianGradientForm
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi := (hessianMetricIntegrability_of_hasCompactSupport_left hφ hV hpos hf hg hfc).2
  simp_rw [heq] at hi
  have hibp := integral_mul_hessianMetricDiffusion_of_hasCompactSupport_left hφ hV hpos hMA hf hg hfc
  simp_rw [heq, integral_neg, neg_neg] at hibp
  constructor
  · convert! hi.neg using 1
    funext x
    exact (neg_neg _).symm
  · exact hibp.symm

end KLS
end

#print axioms KLS.potentialSublevelCutoff_hasCompactSupport
#print axioms KLS.hessianMetricDiffusion_potentialSublevelCutoff
#print axioms KLS.potentialSublevelTail_energy_identity
