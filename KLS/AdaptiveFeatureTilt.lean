import KLS.FiniteFeatureAverage
import KLS.LocalizationNormBridge
import KLS.CovarianceMatrix
import KLS.TiltCumulants
import Mathlib.Data.Fin.Tuple.Basic

/-! The actual matrix-quadratic localization law, with all matrix entries as
finite features. Symmetric Q is included; smoothness holds on the full matrix space. -/
open MeasureTheory ProbabilityTheory Set Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.FiniteFeatureTilt KLS.StandardLocalization

variable {n : ℕ}
abbrev Parameter (n : ℕ) := (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ

def exponent (c : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  (∑ i, c i * x i) - (∑ i, ∑ j, Q i j * x i * x j) / 2

/-- The finite-feature polynomial is the literal linear-minus-quadratic form. -/
theorem exponent_eq_dotProduct (c : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (x : Space n) : exponent c Q x =
      dotProduct c (fun i => x i) -
        dotProduct (fun i => x i) (Q *ᵥ (fun i => x i)) / 2 := by
  change (∑ i, c i * x i) - (∑ i, ∑ j, Q i j * x i * x j) / 2 =
    (∑ i, c i * x i) - (∑ i, x i * (∑ j, Q i j * x j)) / 2
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

def law (μ : Measure (Space n)) (c : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) :=
  μ.tilted (exponent c Q)

def mean (μ : Measure (Space n)) (c : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  fun i => ∫ x, x i ∂law μ c Q

def covariance (μ : Measure (Space n)) (c : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ProbabilityTheory.covariance (fun x : Space n => x i) (fun x => x j) (law μ c Q)

def feature (x : Space n) : Space (n + n * n) :=
  toSpace (Fin.addCases (fun i => x i)
    (fun a => -(x (finProdFinEquiv.symm a).1 * x (finProdFinEquiv.symm a).2) / 2))

def parameter (p : Parameter n) : Space (n + n * n) :=
  toSpace (Fin.addCases p.1 (fun a => p.2 (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2))

theorem continuous_exponent (c : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (exponent c Q) := by
  unfold exponent
  fun_prop

theorem continuous_feature : Continuous (feature (n := n)) := by
  apply continuous_toSpace.comp
  apply continuous_pi
  intro a
  refine Fin.addCases ?_ ?_ a
  · intro i
    simp only [Fin.addCases_left]
    fun_prop
  · intro ij
    simp only [Fin.addCases_right]
    fun_prop

theorem contDiff_parameter : ContDiff ℝ (⊤ : ℕ∞) (parameter (n := n)) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + n * n) => ℝ)).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro a
  refine Fin.addCases ?_ ?_ a
  · intro i
    simp only [Fin.addCases_left]
    fun_prop
  · intro ij
    simp only [Fin.addCases_right]
    fun_prop

theorem exponent_eq_feature_inner (c : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (x : Space n) : exponent c Q x = inner ℝ (parameter (c,Q)) (feature x) := by
  rw [parameter, inner_toSpace_eq]
  simp only [feature, toSpace, WithLp.toLp_ofLp, WithLp.ofLp_toLp,
    Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
  have he : (∑ a : Fin (n * n), Q (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2 *
      (-(x (finProdFinEquiv.symm a).1 * x (finProdFinEquiv.symm a).2) / 2)) =
      ∑ i : Fin n, ∑ j : Fin n, Q i j * (-(x i * x j) / 2) := by
    rw [← (finProdFinEquiv : Fin n × Fin n ≃ Fin (n * n)).sum_comp]
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
  rw [he]
  unfold exponent
  have ht : (∑ i : Fin n, ∑ j : Fin n, Q i j * (-(x i * x j) / 2)) =
      -((∑ i : Fin n, ∑ j : Fin n, Q i j * x i * x j) / 2) := by
    simp only [Finset.sum_div, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [ht]
  ring

variable {μ : Measure (Space n)} [IsProbabilityMeasure μ]

@[simp] theorem law_zero_zero :
    law μ (0 : Fin n → ℝ) (0 : Matrix (Fin n) (Fin n) ℝ) = μ := by
  have he : exponent (0 : Fin n → ℝ) (0 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
    funext x
    simp [exponent]
  simp [law, he]

theorem law_isProbability (hμ : IsCompact μ.support) (c : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) : IsProbabilityMeasure (law μ c Q) :=
  tilted_isProbability_of_compact_support hμ (continuous_exponent c Q)

theorem support_law (hμ : IsCompact μ.support) (c : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) : (law μ c Q).support = μ.support := by
  exact tilted_support_eq hμ (continuous_exponent c Q)

/-- All-order genuine smoothness in all linear and quadratic coefficients. -/
theorem contDiff_average (hμ : IsCompact μ.support) {f : Space n → ℝ} (hf : Integrable f μ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Parameter n => ∫ x, f x ∂law μ p.1 p.2) := by
  have h := (contDiff_featureAverage hμ continuous_feature (q := fun _ => 0) continuous_const hf).comp
    contDiff_parameter
  have he (p : Parameter n) : exponent p.1 p.2 =
      fun x => 0 + inner ℝ (parameter p) (feature x) := by
    funext x
    simpa only [zero_add] using exponent_eq_feature_inner p.1 p.2 x
  convert h using 1
  funext p
  change (∫ x, f x ∂μ.tilted (exponent p.1 p.2)) =
    ∫ x, f x ∂μ.tilted (fun x => 0 + inner ℝ (parameter p) (feature x))
  rw [he]

theorem contDiff_mean (hμ : IsCompact μ.support) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (mean μ)) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_average hμ (integrable_of_continuous_compact_support_measure hμ (by fun_prop))

theorem covariance_eq_moments (hμ : IsCompact μ.support) (c : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    covariance μ c Q i j = (∫ x, x i * x j ∂law μ c Q) - mean μ c Q i * mean μ c Q j := by
  letI := law_isProbability hμ c Q
  exact ProbabilityTheory.covariance_eq_sub
    (memLp_two_continuous_tilted hμ (continuous_exponent c Q) (by fun_prop))
    (memLp_two_continuous_tilted hμ (continuous_exponent c Q) (by fun_prop))

theorem contDiff_covariance (hμ : IsCompact μ.support) (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Parameter n => covariance μ p.1 p.2 i j) := by
  simp_rw [covariance_eq_moments hμ]
  exact (contDiff_average hμ (integrable_of_continuous_compact_support_measure hμ
      (by fun_prop))).sub
    ((contDiff_average hμ (f := fun x => x i)
      (integrable_of_continuous_compact_support_measure hμ (by fun_prop))).mul
    (contDiff_average hμ (f := fun x => x j)
      (integrable_of_continuous_compact_support_measure hμ (by fun_prop))))

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.contDiff_average
#print axioms KLS.AdaptiveLocalization.contDiff_mean
#print axioms KLS.AdaptiveLocalization.contDiff_covariance
