import KLS.LocalWeakAlgebra
import KLS.WeakHessianTensorSymmetry
import KLS.BrascampLiebFiniteEnergy

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter Matrix
open scoped BigOperators ContDiff Topology ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

theorem continuous_weightedDiffusion_C1 {φ g : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hg : ContDiff ℝ 2 g) :
    Continuous (weightedDiffusion φ g) := by
  have he := funext (weightedDiffusion_eq_sum φ g)
  rw [he]
  apply continuous_finsetSum
  intro i _
  exact (contDiff_coordinateHessian hg (m := 0) (by norm_num) i i).continuous.sub
    ((contDiff_coordinateDerivative hg (m := 0) (by norm_num) i).continuous.mul
      (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous)

theorem hasCompactSupport_weightedDiffusion_raw {φ g : Space n → ℝ}
    (hc : HasCompactSupport g) : HasCompactSupport (weightedDiffusion φ g) := by
  have he := funext (weightedDiffusion_eq_sum φ g)
  rw [he]
  convert HasCompactSupport.finset_sum (s := Finset.univ)
    (f := fun i x => coordinateHessian g x i i - coordinateDerivative g i x * coordinateDerivative φ i x)
    (fun i _ => (hasCompactSupport_coordinateHessian hc i i).sub
      (hasCompactSupport_coordinateDerivative hc i).mul_right) using 1
  funext x
  simp only [Finset.sum_apply]

theorem memLp_weightedDiffusion_C1 {φ g : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g) :
    MemLp (weightedDiffusion φ g) 2 (potentialMeasure φ) :=
  memLp_of_continuous_hasCompactSupport hφ.continuous
    (continuous_weightedDiffusion_C1 hφ hg) (hasCompactSupport_weightedDiffusion_raw hc)

theorem integrable_raw_mul_compact_potential
    {φ f ψ : Space n → ℝ} (hφ : Continuous φ)
    (hf : LocallyIntegrable f volume) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun x => f x * ψ x) (potentialMeasure φ) := by
  apply (integrable_potentialMeasure_iff hφ.measurable).mpr
  have hi : Integrable (fun x => f x * (ψ x * Real.exp (-φ x))) volume :=
    integrable_mul_compact_of_locallyIntegrable hf
    (hψ.mul (Real.continuous_exp.comp hφ.neg)) hc.mul_right
  simpa only [mul_assoc] using hi

/-- Local weak derivatives can be paired directly with a compact smooth
diffusion for a C1 density; no weighted graph-closure hypothesis is used. -/
theorem raw_weak_gradient_pairing_eq_neg_diffusion
    {φ f ψ : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hf : LocallyIntegrable f volume)
    (hFl : ∀ i, LocallyIntegrable (F i) volume)
    (hFw : ∀ i, HasLocalWeakCoordinateDerivative f (F i) i)
    (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) :
    (∀ i, Integrable (fun x => F i x * coordinateDerivative ψ i x) (potentialMeasure φ)) ∧
    Integrable (fun x => f x * weightedDiffusion φ ψ x) (potentialMeasure φ) ∧
    (∑ i, ∫ x, F i x * coordinateDerivative ψ i x ∂potentialMeasure φ) =
      -(∫ x, f x * weightedDiffusion φ ψ x ∂potentialMeasure φ) := by
  have hψd (i : Fin n) := (contDiff_coordinateDerivative hψ (m := 1) (by norm_num) i)
  have hFi (i : Fin n) := integrable_raw_mul_compact_potential hφ.continuous (hFl i)
    (hψd i).continuous (hasCompactSupport_coordinateDerivative hc i)
  have hfi := integrable_raw_mul_compact_potential hφ.continuous hf
    (continuous_weightedDiffusion_C1 hφ hψ) (hasCompactSupport_weightedDiffusion_raw hc)
  refine ⟨hFi, hfi, ?_⟩
  let w : Fin n → Space n → ℝ := fun i x => Real.exp (-φ x) * coordinateDerivative ψ i x
  have hw (i : Fin n) : ContDiff ℝ 1 (w i) := hφ.neg.exp.mul (hψd i)
  have hwc (i : Fin n) : HasCompactSupport (w i) :=
    (hasCompactSupport_coordinateDerivative hc i).mul_left
  have hi (i : Fin n) : Integrable (fun x => f x * coordinateDerivative (w i) i x) volume :=
    integrable_mul_compact_of_locallyIntegrable hf
      (contDiff_coordinateDerivative (hw i) (m := 0) (by norm_num) i).continuous
      (hasCompactSupport_coordinateDerivative (hwc i) i)
  have he (i : Fin n) : (∫ x, F i x * coordinateDerivative ψ i x ∂potentialMeasure φ) =
      -(∫ x, f x * coordinateDerivative (w i) i x) := by
    have hh := hFw i (w i) (hw i) (hwc i)
    rw [integral_potentialMeasure hφ.continuous.measurable]
    have hr : (∫ x, (F i x * coordinateDerivative ψ i x) * Real.exp (-φ x)) =
        ∫ x, F i x * w i x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp [w]; ring
    rw [hr]
    linarith
  calc
    _ = ∑ i, -(∫ x, f x * coordinateDerivative (w i) i x) :=
      Finset.sum_congr rfl (fun i _ => he i)
    _ = -(∫ x, ∑ i, f x * coordinateDerivative (w i) i x) := by
      rw [Finset.sum_neg_distrib, integral_finsetSum _ (fun i _ => hi i)]
    _ = _ := by
      rw [integral_potentialMeasure hφ.continuous.measurable]
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [← Finset.mul_sum]
        change f x * (∑ i, coordinateDerivative
          (fun y => Real.exp (-φ y) * coordinateDerivative ψ i y) i x) = _
        rw [← exp_neg_mul_weightedDiffusion_eq_sum_derivative hφ hψ x]
        ring

end KLS
end
