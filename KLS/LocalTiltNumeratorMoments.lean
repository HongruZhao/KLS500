import KLS.LocalTiltSmooth
import KLS.TiltNumeratorMoments

/-! Genuine higher Laplace derivatives under one local radial exponential
envelope, including laws whose Laplace transform is finite only near zero. -/
open MeasureTheory InnerProductSpace Filter Set Metric
open scoped ContDiff Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma LocalNormExponentialDomain.mul_inner {μ : Measure (Space n)}
    {f : Space n → ℝ} {r : ℝ} (hf : LocalNormExponentialDomain μ f r) (v : Space n) :
    LocalNormExponentialDomain μ (fun x => f x * inner ℝ x v) r := by
  refine ⟨hf.1.mul (by fun_prop), ?_⟩
  intro m
  apply ((hf.2 (m+1)).const_mul ‖v‖).mono' (by
    exact ((hf.1.mul (show AEStronglyMeasurable (fun x : Space n => inner ℝ x v) μ by
      fun_prop)).norm.mul (by fun_prop)).mul (by fun_prop))
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul]
  have hh := norm_inner_le_norm (𝕜 := ℝ) x v
  calc
    _ ≤ (‖f x‖ * (‖x‖ * ‖v‖)) * ‖x‖ ^ m * Real.exp (r * ‖x‖) := by gcongr
    _ = _ := by rw [pow_succ]; ring

lemma LocalNormExponentialDomain.mul_innerWord {μ : Measure (Space n)}
    {f : Space n → ℝ} {r : ℝ} (hf : LocalNormExponentialDomain μ f r) (vs : List (Space n)) :
    LocalNormExponentialDomain μ (fun x => f x * innerWordMonomial vs x) r := by
  induction vs with
  | nil => simpa [innerWordMonomial] using hf
  | cons v vs ih =>
    convert ih.mul_inner v using 1
    funext x
    simp only [innerWordMonomial, List.map_cons, List.prod_cons]
    ring

lemma fderiv_tiltNumerator_apply_inner_of_local {μ : Measure (Space n)}
    {f : Space n → ℝ} {r : ℝ} (hf : LocalNormExponentialDomain μ f r)
    {z : Space n} (hz : ‖z‖ < r) (v : Space n) :
    fderiv ℝ (tiltNumerator μ (fun _ => 0) f) z v =
      tiltNumerator μ (fun _ => 0) (fun x => f x * inner ℝ x v) z := by
  rw [(hasFDerivAt_tiltNumerator_of_localNormExponentialDomain hf hz).fderiv,
    ContinuousLinearMap.integral_apply (hf.integrable_tilt_derivative hz.le)]
  unfold tiltNumerator
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [_root_.smul_apply, smul_eq_mul, innerSL_apply_apply, zero_add]
  ring

lemma directionalWordDerivative_tiltNumerator_of_local {μ : Measure (Space n)}
    {f : Space n → ℝ} {r : ℝ} (hf : LocalNormExponentialDomain μ f r)
    (vs : List (Space n)) {z : Space n} (hz : ‖z‖ < r) :
    directionalWordDerivative (tiltNumerator μ (fun _ => 0) f) vs z =
      tiltNumerator μ (fun _ => 0) (fun x => f x * innerWordMonomial vs x) z := by
  induction vs generalizing z with
  | nil => simp [innerWordMonomial]
  | cons v vs ih =>
    have he : directionalWordDerivative (tiltNumerator μ (fun _ => 0) f) vs =ᶠ[𝓝 z]
        tiltNumerator μ (fun _ => 0) (fun x => f x * innerWordMonomial vs x) := by
      filter_upwards [isOpen_ball.mem_nhds (show z ∈ ball (0 : Space n) r by simpa using hz)] with w hw
      exact ih (by simpa using hw)
    rw [directionalWordDerivative_cons, he.fderiv_eq,
      fderiv_tiltNumerator_apply_inner_of_local (hf.mul_innerWord vs) hz]
    unfold tiltNumerator
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [innerWordMonomial, List.map_cons, List.prod_cons]
    ring

lemma directionalWordDerivative_ofFn_on_ball {f : Space n → ℝ} {r : ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (ball 0 r)) {k : ℕ} (m : Fin k → Space n)
    {z : Space n} (hz : z ∈ ball (0 : Space n) r) :
    directionalWordDerivative f (List.ofFn m) z = iteratedFDeriv ℝ k f z m := by
  induction k generalizing z with
  | zero => simp [iteratedFDeriv_zero_apply]
  | succ k ih =>
    rw [List.ofFn_succ]
    change fderiv ℝ (directionalWordDerivative f (List.ofFn (Fin.tail m))) z (m 0) = _
    have he : directionalWordDerivative f (List.ofFn (Fin.tail m)) =ᶠ[𝓝 z]
        fun y => iteratedFDeriv ℝ k f y (Fin.tail m) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with y hy
      exact ih (Fin.tail m) hy
    rw [he.fderiv_eq]
    have hc := hf.contDiffAt (isOpen_ball.mem_nhds hz)
    have hd := (hc.iteratedFDeriv_right (i := k) (m := (1 : ℕ∞ω)) (by simp)).differentiableAt (by norm_num)
    exact (hd.iteratedFDeriv_succ_apply_left' (m := m)).symm

theorem iteratedFDeriv_tiltNumerator_moment_of_local {d : ℕ} {μ : Measure (Space n)}
    {f : Space n → ℝ} {r : ℝ} (hf : LocalNormExponentialDomain μ f r)
    {z : Space n} (hz : ‖z‖ < r) (m : Fin d → Space n) :
    iteratedFDeriv ℝ d (tiltNumerator μ (fun _ => 0) f) z m =
      ∫ x, f x * (∏ j, inner ℝ x (m j)) * Real.exp (inner ℝ z x) ∂μ := by
  rw [← directionalWordDerivative_ofFn_on_ball
    (contDiffOn_tiltNumerator_of_localNormExponentialDomain hf) m (by simpa using hz),
    directionalWordDerivative_tiltNumerator_of_local hf _ hz]
  simp only [tiltNumerator, zero_add, innerWordMonomial, List.map_ofFn, List.prod_ofFn,
    Function.comp_apply]

end KLS
end
