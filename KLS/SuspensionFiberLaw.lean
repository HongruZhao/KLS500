import KLS.LaplaceNoise
import KLS.GaussianExample

/-! Identification of the actual noise-plus-signal pushforward measure with
its suspension density. The change of variables is proved on each real fiber. -/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace KLS

variable {E : Type*} [MeasurableSpace E]

def suspensionFiberEquiv (F : E → ℝ) (hF : Measurable F) (σ : ℝ) (hσ : σ ≠ 0) :
    E × ℝ ≃ᵐ E × ℝ where
  toFun p := (p.1, (p.2 + F p.1) / σ)
  invFun p := (p.1, σ * p.2 - F p.1)
  left_inv p := by
    apply Prod.ext
    · rfl
    · change σ * ((p.2 + F p.1) / σ) - F p.1 = p.2
      field_simp
      ring
  right_inv p := by
    apply Prod.ext
    · rfl
    · change (σ * p.2 - F p.1 + F p.1) / σ = p.2
      field_simp
      ring
  measurable_toFun := by
    change Measurable (fun p : E × ℝ => (p.1, (p.2 + F p.1) / σ))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : E × ℝ => (p.1, σ * p.2 - F p.1))
    fun_prop

lemma suspensionFiberEquiv_map_base (μ : Measure E) [SFinite μ]
    (F : E → ℝ) (hF : Measurable F) {σ : ℝ} (hσ : 0 < σ) :
    (μ.prod volume).map (suspensionFiberEquiv F hF σ hσ.ne') =
      ENNReal.ofReal σ • (μ.prod volume) := by
  have hfiber (x : E) :
      volume.map (fun η : ℝ => (η + F x) / σ) = ENNReal.ofReal σ • volume := by
    have he : (fun η : ℝ => (η + F x) / σ) =
        (fun η : ℝ => σ⁻¹ * η) ∘ (fun η : ℝ => η + F x) := by
      funext η
      simp only [Function.comp_apply, div_eq_mul_inv]
      ring
    rw [he, ← Measure.map_map (by fun_prop) (by fun_prop),
      (measurePreserving_add_right volume (F x)).map_eq,
      Real.map_volume_mul_left (inv_ne_zero hσ.ne')]
    simp only [inv_inv, abs_of_pos hσ]
  have h := (MeasurePreserving.id μ).skew_product
    (g := fun x η => (η + F x) / σ) (by fun_prop) (ae_of_all _ hfiber)
  have he := h.map_eq
  rw [Measure.prod_smul_right] at he
  exact he

def laplaceSuspensionLaw (μ : Measure E) (F : E → ℝ) (β σ : ℝ) : Measure (E × ℝ) :=
  (μ.prod (laplaceNoiseLaw β)).map (fun p => (p.1, (p.2 + F p.1) / σ))

/-- Exact density of the actual pushforward. In particular, no claim that a
chosen density is the law of the signal-plus-noise variable is assumed. -/
theorem laplaceSuspensionLaw_eq_withDensity (μ : Measure E) [SFinite μ]
    (F : E → ℝ) (hF : Measurable F) {β σ : ℝ} (hσ : 0 < σ) :
    laplaceSuspensionLaw μ F β σ = (μ.prod volume).withDensity
      (fun p => ENNReal.ofReal (σ * laplaceNoiseDensity β (σ * p.2 - F p.1))) := by
  let e := suspensionFiberEquiv F hF σ hσ.ne'
  have hρ : Measurable (fun z : E × ℝ => ENNReal.ofReal (laplaceNoiseDensity β z.2)) :=
    ((continuous_laplaceNoiseDensity β).measurable.comp measurable_snd).ennreal_ofReal
  change (μ.prod (laplaceNoiseLaw β)).map e = _
  rw [laplaceNoiseLaw, prod_withDensity_right
    (continuous_laplaceNoiseDensity β).measurable.ennreal_ofReal,
    map_withDensity_measurableEquiv e _ _ hρ,
    suspensionFiberEquiv_map_base μ F hF hσ, withDensity_smul_measure,
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext p
  simp only [Pi.smul_apply, smul_eq_mul, e, suspensionFiberEquiv]
  rw [ENNReal.ofReal_mul hσ.le]
  rfl

theorem isProbabilityMeasure_laplaceSuspensionLaw (μ : Measure E) [IsProbabilityMeasure μ]
    (F : E → ℝ) (hF : Measurable F) {β σ : ℝ} (hβ : 0 < β) :
    IsProbabilityMeasure (laplaceSuspensionLaw μ F β σ) := by
  have : IsProbabilityMeasure (laplaceNoiseLaw β) := isProbabilityMeasure_laplaceNoiseLaw hβ
  unfold laplaceSuspensionLaw
  apply (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2
  infer_instance

end KLS
end
#print axioms KLS.laplaceSuspensionLaw_eq_withDensity
#print axioms KLS.isProbabilityMeasure_laplaceSuspensionLaw
