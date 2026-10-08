import KLS.FiniteFeatureAverage
import KLS.LocalizationCovariance

/-! Joint time-state smoothness of the actual standard-localization moments. -/
open MeasureTheory Set
open scoped Topology BigOperators
noncomputable section
namespace KLS.StandardLocalization
open KLS.FiniteFeatureTilt

variable {n : ℕ}

/-- The first feature records the quadratic time tilt; the remaining features
are the actual Euclidean coordinates. -/
def localizationFeature (x : Space n) : Space (n + 1) :=
  toSpace (Fin.cons (-‖x‖ ^ 2 / 2) (fun i => x i))

def localizationParameter (p : ℝ × (Fin n → ℝ)) : Space (n + 1) :=
  toSpace (Fin.cons p.1 p.2)

theorem continuous_localizationFeature : Continuous (localizationFeature (n := n)) := by
  apply continuous_toSpace.comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    fun_prop
  · simp only [Fin.cons_succ]
    fun_prop

theorem contDiff_localizationParameter :
    ContDiff ℝ (⊤ : ℕ∞) (localizationParameter (n := n)) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using (contDiff_fst : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => p.1))
  · convert (contDiff_apply ℝ ℝ j).comp
      (contDiff_snd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => p.2)) using 1
    funext p
    rfl

theorem exponent_eq_feature_inner (t : ℝ) (c : Fin n → ℝ) (x : Space n) :
    exponent t c x = inner ℝ (localizationParameter (t,c)) (localizationFeature x) := by
  rw [localizationParameter, inner_toSpace_eq]
  simp only [localizationFeature, toSpace, WithLp.toLp_ofLp,
    WithLp.ofLp_toLp, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  unfold exponent
  ring

variable {μ : Measure (Space n)} [IsProbabilityMeasure μ]

/-- Joint C∞ regularity in time and state, for every integrable observable. -/
theorem contDiff_average (hμ : IsCompact μ.support) {f : Space n → ℝ} (hf : Integrable f μ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => ∫ x, f x ∂law μ p.1 p.2) := by
  have h := (contDiff_featureAverage hμ continuous_localizationFeature (q := fun _ => 0) continuous_const hf).comp
    contDiff_localizationParameter
  have he (p : ℝ × (Fin n → ℝ)) : exponent p.1 p.2 =
      fun x => 0 + inner ℝ (localizationParameter p) (localizationFeature x) := by
    funext x
    simpa only [zero_add] using exponent_eq_feature_inner p.1 p.2 x
  convert h using 1
  funext p
  change (∫ x, f x ∂μ.tilted (exponent p.1 p.2)) =
    ∫ x, f x ∂μ.tilted (fun x => 0 + inner ℝ (localizationParameter p) (localizationFeature x))
  rw [he]

theorem contDiff_mean (hμ : IsCompact μ.support) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (mean μ)) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_average hμ (integrable_of_continuous_compact_support_measure hμ (by fun_prop))

theorem contDiff_covariance (hμ : IsCompact μ.support) (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => covariance μ p.1 p.2 i j) := by
  simp_rw [covariance_eq_moments hμ]
  exact (contDiff_average hμ (integrable_of_continuous_compact_support_measure hμ
      (by fun_prop))).sub
    ((contDiff_average hμ (f := fun x => x i)
      (integrable_of_continuous_compact_support_measure hμ (by fun_prop))).mul
    (contDiff_average hμ (f := fun x => x j)
      (integrable_of_continuous_compact_support_measure hμ (by fun_prop))))

end KLS.StandardLocalization
end
#print axioms KLS.StandardLocalization.contDiff_average
#print axioms KLS.StandardLocalization.contDiff_mean
#print axioms KLS.StandardLocalization.contDiff_covariance
