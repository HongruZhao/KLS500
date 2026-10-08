import KLS.CenteredExponential

/-!
# The centered exponential law in the original density-based KLS class

The law is the concrete measure from `CenteredExponential`: the image of the
rate-one exponential law under `y ↦ (y - 1)e₀` in `Space 1`. We identify its
Lebesgue density with the exponential of an affine potential on the closed
half-line and infinity outside that support.

These results concern `HasLogConcaveDensity` and the original `IsKLSMeasure`.
They do not assert compact-set log-concavity or membership in the separate
`admissibleMeasure` class.
-/

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set

noncomputable section
namespace KLS.CenteredExponential

/-- The one-dimensional coordinate isometry, with the standard volume normalization. -/
def coordinateIsometry : ℝ ≃ₗᵢ[ℝ] Space 1 where
  toFun y := PiLp.single 2 (0 : Fin 1) y
  invFun x := x 0
  left_inv y := by simp
  right_inv x := by
    ext i
    fin_cases i
    simp
  map_add' y z := by
    ext i
    fin_cases i
    simp
  map_smul' c y := by
    ext i
    fin_cases i
    simp
  norm_map' y := by simp

/-- A measurable equivalence implementing the centered exponential embedding. -/
def embeddingEquiv : ℝ ≃ᵐ Space 1 where
  toFun := embedding
  invFun x := x 0 + 1
  left_inv y := by simp
  right_inv x := by
    ext i
    fin_cases i
    simp
  measurable_toFun := continuous_embedding.measurable
  measurable_invFun := by
    change Measurable (fun x : Space 1 => x 0 + 1)
    fun_prop

@[simp]
theorem embeddingEquiv_apply (y : ℝ) : embeddingEquiv y = embedding y := rfl

@[simp]
theorem embeddingEquiv_symm_apply (x : Space 1) : embeddingEquiv.symm x = x 0 + 1 := rfl

/-- Translation and the coordinate isometry preserve the exact Lebesgue normalization. -/
theorem measurePreserving_embedding :
    MeasurePreserving embedding (volume : Measure ℝ) (volume : Measure (Space 1)) := by
  have heq : embedding = coordinateIsometry ∘ (fun y : ℝ => y - 1) := by
    funext y
    ext i
    fin_cases i
    simp [coordinateIsometry]
  rw [heq]
  exact coordinateIsometry.measurePreserving.comp (measurePreserving_sub_right volume 1)

private theorem density_transport (e : ℝ ≃ᵐ Space 1) (f : ℝ → ℝ≥0∞)
    (hf : Measurable f) :
    ((volume : Measure ℝ).withDensity f).map e =
      ((volume : Measure ℝ).map e).withDensity (f ∘ e.symm) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg e.measurable,
    lintegral_withDensity_eq_lintegral_mul (g := fun x => g (e x)) volume hf
      (hg.comp e.measurable),
    lintegral_withDensity_eq_lintegral_mul (volume.map e) (hf.comp e.symm.measurable) hg,
    lintegral_map ((hf.comp e.symm.measurable).mul hg) e.measurable]
  simp

/-- The actual density is `exp(-(x₀+1))` on `x₀ ≥ -1`, zero elsewhere. -/
theorem measure_eq_withDensity :
    measure = (volume : Measure (Space 1)).withDensity
      (fun x => exponentialPDF 1 (x 0 + 1)) := by
  change ((volume : Measure ℝ).withDensity (exponentialPDF 1)).map embeddingEquiv = _
  rw [density_transport embeddingEquiv (exponentialPDF 1) (by
    unfold exponentialPDF
    fun_prop)]
  rw [show (volume : Measure ℝ).map embeddingEquiv = (volume : Measure (Space 1)) from
    measurePreserving_embedding.map_eq]
  rfl

/-- The affine potential is finite exactly on the exponential law's closed half-line support. -/
def potential (x : Space 1) : WithTop ℝ :=
  if -1 ≤ x 0 then ((x 0 + 1 : ℝ) : WithTop ℝ) else ⊤

/-- The epigraph is the intersection of two affine half-spaces. -/
theorem potential_extendedConvex : ExtendedConvex potential := by
  have hepi : {p : Space 1 × ℝ | potential p.1 ≤ (p.2 : WithTop ℝ)} =
      {p | -1 ≤ p.1 0 ∧ p.1 0 + 1 ≤ p.2} := by
    ext p
    change (potential p.1 ≤ (p.2 : WithTop ℝ)) ↔ (-1 ≤ p.1 0 ∧ p.1 0 + 1 ≤ p.2)
    by_cases hp : -1 ≤ p.1 0
    · rw [potential, ite_eq_left hp, WithTop.coe_le_coe]
      simp only [hp, true_and]
    · simp [potential, hp]
  rw [ExtendedConvex, hepi]
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  change -1 ≤ (a • x.1 + b • y.1) 0 ∧
    (a • x.1 + b • y.1) 0 + 1 ≤ a * x.2 + b * y.2
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  constructor <;> nlinarith [mul_nonneg ha (by linarith : 0 ≤ x.1 0 + 1),
    mul_nonneg hb (by linarith : 0 ≤ y.1 0 + 1),
    mul_nonneg ha (by linarith : 0 ≤ x.2 - (x.1 0 + 1)),
    mul_nonneg hb (by linarith : 0 ≤ y.2 - (y.1 0 + 1))]

/-- Pointwise equality includes the boundary point of the support. -/
theorem expNegPotential_potential (x : Space 1) :
    expNegPotential (potential x) = exponentialPDF 1 (x 0 + 1) := by
  by_cases hx : -1 ≤ x 0
  · have hx' : 0 ≤ x 0 + 1 := by linarith
    rw [potential, ite_eq_left hx]
    change ENNReal.ofReal (Real.exp (-(x 0 + 1))) = _
    rw [exponentialPDF_of_nonneg hx']
    simp
  · have hx' : ¬ 0 ≤ x 0 + 1 := by linarith
    simp [potential, hx, expNegPotential, exponentialPDF_eq, hx']

/-- A genuine log-concave-density representation of the concrete centered exponential law. -/
theorem hasLogConcaveDensity : HasLogConcaveDensity measure := by
  refine ⟨potential, potential_extendedConvex, ?_, ?_⟩
  · simp_rw [expNegPotential_potential]
    unfold exponentialPDF
    fun_prop
  · simp_rw [expNegPotential_potential]
    exact measure_eq_withDensity

/-- The centered exponential law is in the original density-based KLS class.
This assertion does not identify it with the compact-set measure class. -/
theorem isKLSMeasure : IsKLSMeasure measure where
  isProb := inferInstance
  absCont := hasLogConcaveDensity.absolutelyContinuousLebesgue
  logConcave := hasLogConcaveDensity
  isotropic := isIsotropic

end KLS.CenteredExponential
end

#print axioms KLS.CenteredExponential.measurePreserving_embedding
#print axioms KLS.CenteredExponential.measure_eq_withDensity
#print axioms KLS.CenteredExponential.potential_extendedConvex
#print axioms KLS.CenteredExponential.hasLogConcaveDensity
#print axioms KLS.CenteredExponential.isKLSMeasure
