import KLS.IsotropicGaussianSmoothing

/-!
# The actual smooth convex potential after isotropic normalization

Scalar change of variables is applied to the actual convolution density.
The resulting finite potential is smooth and convex on the whole space.
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal MeasureTheory ContDiff Topology

noncomputable section
namespace KLS

theorem map_smul_withDensity_ofReal {n : ℕ} {f : Space n → ℝ} (hf : Measurable f)
    {a : ℝ} (ha : a ≠ 0) :
    ((volume : Measure (Space n)).withDensity (fun x => ENNReal.ofReal (f x))).map
        (fun x => a • x) =
      (volume : Measure (Space n)).withDensity
        (fun x => ENNReal.ofReal (|(a ^ n)⁻¹| * f (a⁻¹ • x))) := by
  let e : Space n ≃ᵐ Space n := (Homeomorph.smulOfNeZero a ha).toMeasurableEquiv
  change ((volume : Measure (Space n)).withDensity (fun x => ENNReal.ofReal (f x))).map e = _
  rw [map_withDensity_measurableEquiv e _ _ hf.ennreal_ofReal]
  have he : (e : Space n → Space n) = fun x => a • x := by
    ext x
    simp [e, Homeomorph.smulOfNeZero, Homeomorph.smul, Units.smul_def]
  rw [he, Measure.map_addHaar_smul volume ha]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [withDensity_smul_measure, ← withDensity_smul _
    (hf.ennreal_ofReal.comp e.symm.measurable)]
  congr 1
  funext x
  change ENNReal.ofReal |(a ^ n)⁻¹| * ENNReal.ofReal (f (a⁻¹ • x)) = _
  exact (ENNReal.ofReal_mul (abs_nonneg _)).symm

def scalarTransformedPotential {n : ℕ} (V : Space n → ℝ) (a : ℝ) (x : Space n) : ℝ :=
  V (a⁻¹ • x) - Real.log |(a ^ n)⁻¹|

theorem scalarTransformedPotential_contDiff {n : ℕ} {V : Space n → ℝ} {m : ℕ∞}
    (hV : ContDiff ℝ m V) (a : ℝ) : ContDiff ℝ m (scalarTransformedPotential V a) := by
  unfold scalarTransformedPotential
  have hl : ContDiff ℝ m (fun x : Space n => a⁻¹ • x) := by fun_prop
  exact (hV.comp hl).sub contDiff_const

theorem scalarTransformedPotential_convex {n : ℕ} {V : Space n → ℝ}
    (hV : ConvexOn ℝ univ V) (a : ℝ) :
    ConvexOn ℝ univ (scalarTransformedPotential V a) := by
  have hh : ConvexOn ℝ univ (fun x : Space n => V (a⁻¹ • x)) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ s t hs ht hst
    simpa only [smul_add, smul_smul, mul_comm a⁻¹] using
      hV.2 (mem_univ (a⁻¹ • x)) (mem_univ (a⁻¹ • y)) hs ht hst
  convert hh.add_const (-Real.log |(a ^ n)⁻¹|) using 1
  ext x
  simp [scalarTransformedPotential, sub_eq_add_neg]

theorem map_smul_exp_potential {n : ℕ} {V : Space n → ℝ} (hV : Measurable V)
    {a : ℝ} (ha : a ≠ 0) :
    ((volume : Measure (Space n)).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-V x)))).map (fun x => a • x) =
      (volume : Measure (Space n)).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-scalarTransformedPotential V a x))) := by
  rw [map_smul_withDensity_ofReal (f := fun x => Real.exp (-V x)) (by fun_prop) ha]
  congr 1
  funext x
  unfold scalarTransformedPotential
  rw [neg_sub, Real.exp_sub, Real.exp_log (abs_pos.mpr (inv_ne_zero (pow_ne_zero n ha))),
    Real.exp_neg, div_eq_mul_inv]

def isotropicGaussianPotential {n : ℕ} (μ : Measure (Space n)) (r : ℝ) : Space n → ℝ :=
  scalarTransformedPotential (gaussianSmoothedPotential μ r) (gaussianNormalization r)

theorem isotropicGaussianPotential_contDiff {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hc : IsCompact μ.support) {r : ℝ} (hr : r ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (isotropicGaussianPotential μ r) :=
  scalarTransformedPotential_contDiff (gaussianSmoothedPotential_contDiff hc hr) _

theorem admissibleMeasure.isotropicGaussianPotential_convex {n : ℕ}
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (hc : IsCompact μ.support)
    {r : ℝ} (hr : r ≠ 0) : ConvexOn ℝ univ (isotropicGaussianPotential μ r) :=
  scalarTransformedPotential_convex (hμ.gaussianSmoothedPotential_convex hc hr) _

theorem admissibleMeasure.isotropicGaussianSmoothing_eq_exp_potential {n : ℕ}
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (hc : IsCompact μ.support)
    {r : ℝ} (hr : r ≠ 0) : KLS.isotropicGaussianSmoothing μ r =
      (volume : Measure (Space n)).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-isotropicGaussianPotential μ r x))) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  rw [KLS.isotropicGaussianSmoothing, hμ.gaussianSmoothing_eq_exp_potential hc hr]
  exact map_smul_exp_potential (gaussianSmoothedPotential_contDiff hc hr).continuous.measurable
    (gaussianNormalization_pos r).ne'

end KLS
end

#print axioms KLS.map_smul_withDensity_ofReal
#print axioms KLS.isotropicGaussianPotential_contDiff
#print axioms KLS.admissibleMeasure.isotropicGaussianPotential_convex
#print axioms KLS.admissibleMeasure.isotropicGaussianSmoothing_eq_exp_potential
