import KLS.WeightedTiltSmooth
import KLS.DirectionalWordSymmetry

/-! All genuine mixed derivatives of the unnormalized tilt numerator are
polynomial moments. These identities will give continuity in the L2 signal. -/

open MeasureTheory Filter
open scoped ContDiff BigOperators
noncomputable section
namespace KLS

lemma NormExponentialDomain.mul_inner {n : ℕ} {μ : Measure (Space n)}
    {f : Space n → ℝ} (hf : NormExponentialDomain μ f) (v : Space n) :
    NormExponentialDomain μ (fun x => f x * inner ℝ x v) := by
  refine ⟨hf.1.mul (by fun_prop), ?_⟩
  intro m a
  apply ((hf.2 (m + 1) a).const_mul ‖v‖).mono' (by
    exact ((hf.1.mul (show AEStronglyMeasurable (fun x : Space n => inner ℝ x v) μ by
      fun_prop)).norm.mul (by fun_prop)).mul (by fun_prop))
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul]
  have hh := norm_inner_le_norm (𝕜 := ℝ) x v
  calc
    _ ≤ (‖f x‖ * (‖x‖ * ‖v‖)) * ‖x‖ ^ m * Real.exp (a * ‖x‖) := by gcongr
    _ = _ := by rw [pow_succ]; ring

def innerWordMonomial {n : ℕ} (vs : List (Space n)) (x : Space n) : ℝ :=
  (vs.map (fun v => inner ℝ x v)).prod

lemma NormExponentialDomain.mul_innerWord {n : ℕ} {μ : Measure (Space n)}
    {f : Space n → ℝ} (hf : NormExponentialDomain μ f) (vs : List (Space n)) :
    NormExponentialDomain μ (fun x => f x * innerWordMonomial vs x) := by
  induction vs with
  | nil => simpa [innerWordMonomial] using hf
  | cons v vs ih =>
    convert ih.mul_inner v using 1
    funext x
    simp only [innerWordMonomial, List.map_cons, List.prod_cons]
    ring

lemma fderiv_tiltNumerator_apply_inner {n : ℕ} {μ : Measure (Space n)}
    {f : Space n → ℝ} (hf : NormExponentialDomain μ f) (z v : Space n) :
    fderiv ℝ (tiltNumerator μ (fun _ => 0) f) z v =
      tiltNumerator μ (fun _ => 0) (fun x => f x * inner ℝ x v) z := by
  rw [(hasFDerivAt_tiltNumerator_of_normExponentialDomain hf z).fderiv,
    ContinuousLinearMap.integral_apply (hf.integrable_tilt_derivative z)]
  unfold tiltNumerator
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [_root_.smul_apply, smul_eq_mul, innerSL_apply_apply, zero_add]
  ring

lemma directionalWordDerivative_tiltNumerator {n : ℕ} {μ : Measure (Space n)}
    {f : Space n → ℝ} (hf : NormExponentialDomain μ f) (vs : List (Space n)) :
    directionalWordDerivative (tiltNumerator μ (fun _ => 0) f) vs =
      tiltNumerator μ (fun _ => 0) (fun x => f x * innerWordMonomial vs x) := by
  induction vs with
  | nil => simp [innerWordMonomial]
  | cons v vs ih =>
    funext z
    rw [directionalWordDerivative_cons, ih,
      fderiv_tiltNumerator_apply_inner (hf.mul_innerWord vs)]
    unfold tiltNumerator
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [innerWordMonomial, List.map_cons, List.prod_cons]
    ring

theorem iteratedFDeriv_tiltNumerator_moment {n d : ℕ} {μ : Measure (Space n)}
    {f : Space n → ℝ} (hf : NormExponentialDomain μ f) (z : Space n) (m : Fin d → Space n) :
    iteratedFDeriv ℝ d (tiltNumerator μ (fun _ => 0) f) z m =
      ∫ x, f x * (∏ j, inner ℝ x (m j)) * Real.exp (inner ℝ z x) ∂μ := by
  rw [← directionalWordDerivative_ofFn (contDiff_tiltNumerator_of_normExponentialDomain hf),
    directionalWordDerivative_tiltNumerator hf]
  simp only [tiltNumerator, zero_add, innerWordMonomial, List.map_ofFn, List.prod_ofFn,
    Function.comp_apply]

end KLS
end
#print axioms KLS.iteratedFDeriv_tiltNumerator_moment
