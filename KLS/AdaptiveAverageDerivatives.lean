import KLS.AdaptiveCovarianceExpectation

/-! Genuine state derivatives of actual tilted averages of any integrable observable. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.AdaptiveLocalization
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def coordinateAverage (μ : Measure (Space n)) (f : Space n → ℝ) (z : Fin (n+n*n) → ℝ) : ℝ :=
  ∫ x, f x ∂law μ (decodeState z).1 (decodeState z).2

def coordinateAverageGradient (μ : Measure (Space n)) (f : Space n → ℝ) :=
  fderiv ℝ (coordinateAverage μ f)

def coordinateAverageHessian (μ : Measure (Space n)) (f : Space n → ℝ) :=
  fderiv ℝ (coordinateAverageGradient μ f)

theorem contDiff_coordinateAverage (hμ : IsCompact μ.support) {f : Space n → ℝ} (hf : Integrable f μ) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateAverage μ f) :=
  (contDiff_average hμ hf).comp contDiff_decodeState

theorem hasFDerivAt_coordinateAverage (hμ : IsCompact μ.support) {f : Space n → ℝ} (hf : Integrable f μ)
    (z : Fin (n+n*n) → ℝ) :
    HasFDerivAt (coordinateAverage μ f) (coordinateAverageGradient μ f z) z :=
  ((contDiff_coordinateAverage hμ hf).differentiable (by simp) z).hasFDerivAt

theorem contDiff_coordinateAverageGradient (hμ : IsCompact μ.support) {f : Space n → ℝ}
    (hf : Integrable f μ) : ContDiff ℝ (⊤ : ℕ∞) (coordinateAverageGradient μ f) :=
  (contDiff_coordinateAverage hμ hf).fderiv_right (m := (⊤ : ℕ∞)) (by simp)

theorem hasFDerivAt_coordinateAverageGradient (hμ : IsCompact μ.support) {f : Space n → ℝ}
    (hf : Integrable f μ) (z : Fin (n+n*n) → ℝ) :
    HasFDerivAt (coordinateAverageGradient μ f) (coordinateAverageHessian μ f z) z :=
  ((contDiff_coordinateAverageGradient hμ hf).differentiable (by simp) z).hasFDerivAt

theorem hasDerivAt_coordinateAverage_line (hμ : IsCompact μ.support) {f : Space n → ℝ}
    (hf : Integrable f μ) (z v : Fin (n+n*n) → ℝ) (u : ℝ) :
    HasDerivAt (fun a => coordinateAverage μ f (z+a•v))
      (coordinateAverage μ (fun x => f x * coordinateScore v x) (z+u•v) -
        coordinateAverage μ f (z+u•v) * coordinateAverage μ (coordinateScore v) (z+u•v)) u := by
  have hd := hasDerivAt_tiltAverage hμ
    (continuous_exponent (decodeState z).1 (decodeState z).2) (continuous_coordinateScore v) hf u
  simpa only [coordinateAverage, law, tiltAverage, coordinate_exponent_line] using hd

theorem coordinateAverageGradient_apply (hμ : IsCompact μ.support) {f : Space n → ℝ}
    (hf : Integrable f μ) (z v : Fin (n+n*n) → ℝ) :
    coordinateAverageGradient μ f z v =
      coordinateAverage μ (fun x => f x * coordinateScore v x) z -
        coordinateAverage μ f z * coordinateAverage μ (coordinateScore v) z := by
  have hp : HasDerivAt (fun u : ℝ => z + u • v) v 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z using 1 <;> simp
  have hc := (hasFDerivAt_coordinateAverage hμ hf z).comp_hasDerivAt_of_eq 0 hp (by simp)
  have hc' : HasDerivAt (fun u : ℝ => coordinateAverage μ f (z+u•v)) (coordinateAverageGradient μ f z v) 0 := by
    convert hc using 1
    funext u
    rfl
  simpa only [zero_smul, add_zero] using hc'.unique (hasDerivAt_coordinateAverage_line hμ hf z v 0)

/-- The diagonal second derivative is computed from three actual normalized moments. -/
theorem coordinateAverageHessian_apply_self (hμ : IsCompact μ.support) {f : Space n → ℝ}
    (hf : Integrable f μ) (z v : Fin (n+n*n) → ℝ) :
    coordinateAverageHessian μ f z v v =
      coordinateAverage μ (fun x => f x * (coordinateScore v x)^2) z -
        2*coordinateAverage μ (fun x => f x * coordinateScore v x) z * coordinateAverage μ (coordinateScore v) z -
        coordinateAverage μ f z * coordinateAverage μ (fun x => (coordinateScore v x)^2) z +
        2*coordinateAverage μ f z * (coordinateAverage μ (coordinateScore v) z)^2 := by
  have hs : Integrable (coordinateScore v) μ :=
    integrable_of_continuous_compact_support_measure hμ (continuous_coordinateScore v)
  have hfs : Integrable (fun x => f x*coordinateScore v x) μ :=
    integrable_mul_continuous_of_compact_support hμ hf (continuous_coordinateScore v)
  have hp : HasDerivAt (fun u : ℝ => z+u•v) v 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z using 1 <;> simp
  have hc := (hasFDerivAt_coordinateAverageGradient hμ hf z).comp_hasDerivAt_of_eq 0 hp (by simp)
  have hc' : HasDerivAt (fun u : ℝ => coordinateAverageGradient μ f (z+u•v) v)
      (coordinateAverageHessian μ f z v v) 0 := by
    convert hc.clm_apply (hasDerivAt_const (0 : ℝ) v) using 1 <;> simp
  have hd := (hasDerivAt_coordinateAverage_line hμ hfs z v 0).sub
    ((hasDerivAt_coordinateAverage_line hμ hf z v 0).mul (hasDerivAt_coordinateAverage_line hμ hs z v 0))
  have heq : (fun u : ℝ => coordinateAverageGradient μ f (z+u•v) v) =
      fun u : ℝ => coordinateAverage μ (fun x => f x*coordinateScore v x) (z+u•v) -
        coordinateAverage μ f (z+u•v)*coordinateAverage μ (coordinateScore v) (z+u•v) := by
    funext u
    exact coordinateAverageGradient_apply hμ hf _ _
  rw [heq] at hc'
  have he := hc'.unique hd
  simp only [zero_smul, add_zero] at he
  rw [he]
  have hfs2 : (fun x => f x*coordinateScore v x*coordinateScore v x) =
      fun x => f x*(coordinateScore v x)^2 := by funext x; ring
  have hs2 : (fun x => coordinateScore v x*coordinateScore v x) = fun x => (coordinateScore v x)^2 := by
    funext x
    ring
  rw [hfs2, hs2]
  ring

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.coordinateAverageHessian_apply_self
