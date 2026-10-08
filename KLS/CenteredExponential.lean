import KLS.ExponentialMoments
import KLS.IsotropicLowerBound
import KLS.RouteArithmetic
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# A concrete centered exponential measure and a Poincaré lower bound

This module maps mathlib's standard exponential law into `Space 1`, subtracting
its mean. It proves probability, isotropy, and an actual optimal Poincaré lower
bound of four via exponential test functions.

Compact-set log-concavity and membership in `admissibleMeasure` are separate
obligations. The theorem below therefore does not by itself assert a lower
bound for `universalPoincareConstant`.
-/

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Set Filter InnerProductSpace

noncomputable section
namespace KLS.CenteredExponential

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

def embedding (y : ℝ) : Space 1 :=
  (y - 1) • PiLp.single 2 (0 : Fin 1) (1 : ℝ)

@[fun_prop]
theorem continuous_embedding : Continuous embedding := by
  unfold embedding
  fun_prop

@[simp]
theorem embedding_apply (y : ℝ) (i : Fin 1) : embedding y i = y - 1 := by
  fin_cases i
  simp [embedding]

def measure : Measure (Space 1) := (expMeasure 1).map embedding

instance : IsProbabilityMeasure measure := by
  unfold measure
  infer_instance

theorem integral_measure (f : Space 1 → ℝ) (hf : Continuous f) :
    (∫ x, f x ∂measure) = ∫ y : ℝ, f (embedding y) ∂expMeasure 1 := by
  unfold measure
  exact integral_map continuous_embedding.measurable.aemeasurable hf.aestronglyMeasurable

theorem memLp_coordinate (i : Fin 1) :
    MemLp (fun x : Space 1 => x i) 2 measure := by
  unfold measure
  apply (memLp_map_measure_iff (by fun_prop)
    continuous_embedding.measurable.aemeasurable).mpr
  simpa [Function.comp_def] using expMeasure_one_memLp_centered

theorem integral_coordinate (i : Fin 1) :
    (∫ x : Space 1, x i ∂measure) = 0 := by
  rw [integral_measure _ (by fun_prop)]
  simpa using expMeasure_one_integral_centered

theorem integral_coordinate_sq (i : Fin 1) :
    (∫ x : Space 1, (x i) ^ 2 ∂measure) = 1 := by
  have h := ProbabilityTheory.variance_eq_sub expMeasure_one_memLp_centered
  rw [expMeasure_one_variance_centered, expMeasure_one_integral_centered] at h
  simp only [zero_pow (by decide : 2 ≠ 0), sub_zero] at h
  rw [integral_measure _ (by fun_prop)]
  simpa using h.symm

/-- Probability and all isotropic moment/integrability requirements hold for
the actual centered exponential law in Euclidean dimension one. -/
theorem isIsotropic : IsIsotropic measure := by
  have hi : ∀ i : Fin 1, Integrable (fun x : Space 1 => x i) measure :=
    fun i => (memLp_coordinate i).integrable (by norm_num)
  refine ⟨Integrable.of_eval_piLp hi, ?_, ?_, ?_⟩
  · ext i
    rw [eval_integral_piLp hi i, integral_coordinate]
    rfl
  · intro i j
    exact (memLp_coordinate i).integrable_mul (memLp_coordinate j)
  · ext i j
    fin_cases i
    fin_cases j
    simpa [secondMomentMatrix, pow_two] using integral_coordinate_sq (0 : Fin 1)

def test (a : ℝ) (x : Space 1) : ℝ := Real.exp (a * (x 0 + 1))

@[fun_prop]
theorem continuous_test (a : ℝ) : Continuous (test a) := by
  unfold test
  fun_prop

theorem locallyLipschitz_test (a : ℝ) : LocallyLipschitz (test a) := by
  apply ContDiff.locallyLipschitz (𝕂 := ℝ)
  unfold test
  fun_prop

@[simp]
theorem test_embedding (a y : ℝ) : test a (embedding y) = Real.exp (a * y) := by
  simp [test]

theorem test_sq (a : ℝ) (x : Space 1) : (test a x) ^ 2 = test (2 * a) x := by
  unfold test
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem integrable_test (a : ℝ) (ha : a < 1) : Integrable (test a) measure := by
  unfold measure
  apply (integrable_map_measure (continuous_test a).aestronglyMeasurable
    continuous_embedding.measurable.aemeasurable).mpr
  simpa [Function.comp_def] using (expMeasure_one_exponential_moment a ha).1

theorem integral_test (a : ℝ) (ha : a < 1) :
    (∫ x, test a x ∂measure) = 1 / (1 - a) := by
  rw [integral_measure _ (continuous_test a)]
  simpa using (expMeasure_one_exponential_moment a ha).2

theorem integrable_test_sq (a : ℝ) (ha : a < 1 / 2) :
    Integrable (fun x => (test a x) ^ 2) measure := by
  simp_rw [test_sq]
  exact integrable_test (2 * a) (by linarith)

theorem memLp_test (a : ℝ) (ha : a < 1 / 2) : MemLp (test a) 2 measure :=
  (memLp_two_iff_integrable_sq (continuous_test a).aestronglyMeasurable).mpr
    (integrable_test_sq a ha)

theorem integral_test_sq (a : ℝ) (ha : a < 1 / 2) :
    (∫ x, (test a x) ^ 2 ∂measure) = 1 / (1 - 2 * a) := by
  simp_rw [test_sq]
  exact integral_test (2 * a) (by linarith)

theorem variance_test (a : ℝ) (ha : a < 1 / 2) :
    KLS.variance measure (test a) =
      ENNReal.ofReal (1 / (1 - 2 * a) - (1 / (1 - a)) ^ 2) := by
  rw [KLS.variance, ← ProbabilityTheory.ofReal_variance (memLp_test a ha),
    ProbabilityTheory.variance_eq_sub (memLp_test a ha)]
  change ENNReal.ofReal ((∫ x, (test a x) ^ 2 ∂measure) -
    (∫ x, test a x ∂measure) ^ 2) = _
  rw [integral_test_sq a ha, integral_test a (by linarith)]

theorem gradient_test (a : ℝ) (x : Space 1) :
    gradient (test a) x = (a * test a x) • PiLp.single 2 (0 : Fin 1) (1 : ℝ) := by
  have hd := (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).hasFDerivAt
    (x := x)).add_const 1 |>.const_mul a).exp
  simp only [EuclideanSpace.coe_proj] at hd
  apply (toDual ℝ (Space 1)).injective
  rw [toDual_gradient]
  change fderiv ℝ (fun y : Space 1 => Real.exp (a * (y 0 + 1))) x = _
  rw [hd.fderiv]
  ext y
  simp [toDual_apply_apply, EuclideanSpace.inner_single_left,
    test, mul_assoc, mul_left_comm]

theorem norm_gradient_test_sq (a : ℝ) (x : Space 1) :
    ‖gradient (test a) x‖ ^ 2 = a ^ 2 * (test a x) ^ 2 := by
  simp [gradient_test, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

theorem energy_test (a : ℝ) (ha : a < 1 / 2) :
    energy measure (test a) = ENNReal.ofReal (a ^ 2 / (1 - 2 * a)) := by
  unfold energy
  simp_rw [norm_gradient_test_sq]
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((integrable_test_sq a ha).const_mul (a ^ 2))
    (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg a) (sq_nonneg (test a x)))]
  rw [integral_const_mul, integral_test_sq a ha]
  congr 1
  ring

/-- Every finite admissible Poincaré constant for this actual measure is at
least four. The tests have finite energy, established by the integral formula. -/
theorem four_le_of_poincare_constant {C : ℝ≥0}
    (hC : C ∈ poincareConstants measure) : (4 : ℝ≥0∞) ≤ (C : ℝ≥0∞) := by
  have hfour : (4 : ℝ) ≤ C := by
    apply RouteArithmetic.four_le_of_scalar_ratio_bounds
    intro a ha ha2
    have h := hC (test a) ⟨locallyLipschitz_test a, memLp_test a ha2⟩
    rw [variance_test a ha2, energy_test a ha2] at h
    have he : 0 < a ^ 2 / (1 - 2 * a) :=
      RouteArithmetic.exponential_energy_expression_pos a ha ha2
    have hreal : 1 / (1 - 2 * a) - (1 / (1 - a)) ^ 2 ≤
        (C : ℝ) * (a ^ 2 / (1 - 2 * a)) := by
      apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg C.coe_nonneg he.le)).mp
      simpa only [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal] using h
    have hratio := (div_le_iff₀ he).mpr hreal
    rwa [RouteArithmetic.exponential_moment_ratio_algebra a ha ha2] at hratio
  simpa using ENNReal.ofReal_le_ofReal hfour

/-- A genuine lower bound for the imported optimal constant of a concrete
isotropic probability measure. Full-class admissibility is not asserted. -/
theorem four_le_poincareConstant : 4 ≤ poincareConstant measure := by
  apply le_poincareConstant_of_forall
  intro C hC
  exact four_le_of_poincare_constant hC

end KLS.CenteredExponential
end

#print axioms KLS.CenteredExponential.isIsotropic
#print axioms KLS.CenteredExponential.memLp_test
#print axioms KLS.CenteredExponential.gradient_test
#print axioms KLS.CenteredExponential.energy_test
#print axioms KLS.CenteredExponential.four_le_poincareConstant
