import KLS.AdaptiveExponentialAverage

/-! Actual first and second state derivatives of the logarithmic MGF. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.AdaptiveLocalization
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def coordinateLogMGF (μ : Measure (Space n)) (w : Space n) (z : Fin (n+n*n) → ℝ) : ℝ :=
  Real.log (coordinateAverage μ (exponentialObservable w) z)

def coordinateLogMGFGradient (μ : Measure (Space n)) (w : Space n) :=
  fderiv ℝ (coordinateLogMGF μ w)

def coordinateLogMGFHessian (μ : Measure (Space n)) (w : Space n) :=
  fderiv ℝ (coordinateLogMGFGradient μ w)

theorem integrable_exponentialObservable (hμ : IsCompact μ.support) (w : Space n) :
    Integrable (exponentialObservable w) μ :=
  integrable_of_continuous_compact_support_measure hμ (continuous_exponentialObservable w)

theorem contDiff_coordinateLogMGF (hμ : IsCompact μ.support) (w : Space n) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateLogMGF μ w) :=
  (contDiff_coordinateAverage hμ (integrable_exponentialObservable hμ w)).log
    (fun z => (coordinateMGF_pos hμ w z).ne')

theorem contDiff_coordinateLogMGFGradient (hμ : IsCompact μ.support) (w : Space n) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateLogMGFGradient μ w) :=
  (contDiff_coordinateLogMGF hμ w).fderiv_right (m := (⊤ : ℕ∞)) (by simp)

theorem coordinateLogMGFGradient_apply (hμ : IsCompact μ.support) (w : Space n)
    (z v : Fin (n+n*n) → ℝ) :
    coordinateLogMGFGradient μ w z v =
      coordinateAverageGradient μ (exponentialObservable w) z v /
        coordinateAverage μ (exponentialObservable w) z := by
  have hd := (hasFDerivAt_coordinateAverage hμ (integrable_exponentialObservable hμ w) z).log
    (coordinateMGF_pos hμ w z).ne'
  change fderiv ℝ (fun z => Real.log (coordinateAverage μ (exponentialObservable w) z)) z v = _
  rw [hd.fderiv]
  simp only [smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

/-- Genuine diagonal Hessian of log M, computed by differentiating the first derivative. -/
theorem coordinateLogMGFHessian_apply_self (hμ : IsCompact μ.support) (w : Space n)
    (z v : Fin (n+n*n) → ℝ) :
    coordinateLogMGFHessian μ w z v v =
      coordinateAverageHessian μ (exponentialObservable w) z v v /
        coordinateAverage μ (exponentialObservable w) z -
      (coordinateAverageGradient μ (exponentialObservable w) z v /
        coordinateAverage μ (exponentialObservable w) z)^2 := by
  have hf := integrable_exponentialObservable hμ w
  have hp : HasDerivAt (fun u : ℝ => z+u•v) v 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z using 1 <;> simp
  have hl := (((contDiff_coordinateLogMGFGradient hμ w).differentiable (by simp) z).hasFDerivAt).comp_hasDerivAt_of_eq 0 hp (by simp)
  have hl' : HasDerivAt (fun u : ℝ => coordinateLogMGFGradient μ w (z+u•v) v)
      (coordinateLogMGFHessian μ w z v v) 0 := by
    convert hl.clm_apply (hasDerivAt_const (0 : ℝ) v) using 1 <;> simp [coordinateLogMGFHessian]
  have hA := (hasFDerivAt_coordinateAverageGradient hμ hf z).comp_hasDerivAt_of_eq 0 hp (by simp)
  have hA' : HasDerivAt (fun u : ℝ => coordinateAverageGradient μ (exponentialObservable w) (z+u•v) v)
      (coordinateAverageHessian μ (exponentialObservable w) z v v) 0 := by
    convert hA.clm_apply (hasDerivAt_const (0 : ℝ) v) using 1 <;> simp
  have hM := (hasFDerivAt_coordinateAverage hμ hf z).comp_hasDerivAt_of_eq 0 hp (by simp)
  have hM' : HasDerivAt (fun u : ℝ => coordinateAverage μ (exponentialObservable w) (z+u•v))
      (coordinateAverageGradient μ (exponentialObservable w) z v) 0 := by
    convert hM using 1
    funext u
    rfl
  have hD := hA'.div hM' (by simpa only [zero_smul, add_zero] using (coordinateMGF_pos hμ w z).ne')
  simp_rw [coordinateLogMGFGradient_apply hμ w] at hl'
  have he := hl'.unique hD
  simp only [zero_smul, add_zero] at he
  rw [he]
  field_simp

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.coordinateLogMGFHessian_apply_self
