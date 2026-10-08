import KLS.WeightedTiltSmooth

/-! Genuine exponential moments for graph pushforwards of observables with
at most linear growth. These support noncompact suspension derivatives. -/

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology BigOperators
noncomputable section
namespace KLS

lemma integrable_norm_pow_exp_norm_of_all_exponential_moments {n : ℕ}
    {μ : Measure (Space n)}
    (hμ : ∀ a : ℝ, Integrable (fun x => Real.exp (a * ‖x‖)) μ) (m : ℕ) (a : ℝ) :
    Integrable (fun x => ‖x‖ ^ m * Real.exp (a * ‖x‖)) μ := by
  apply ((hμ (a + 1)).const_mul (m.factorial : ℝ)).mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hm : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have hp := (div_le_iff₀ hm).mp (Real.pow_div_factorial_le_exp ‖x‖ (norm_nonneg x) m)
  calc
    _ ≤ (Real.exp ‖x‖ * (m.factorial : ℝ)) * Real.exp (a * ‖x‖) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by
      rw [mul_comm (Real.exp ‖x‖) (m.factorial : ℝ), mul_assoc, ← Real.exp_add]
      congr 2
      ring

lemma normExponentialDomain_one_of_all_exponential_moments {n : ℕ}
    {μ : Measure (Space n)}
    (hμ : ∀ a : ℝ, Integrable (fun x => Real.exp (a * ‖x‖)) μ) :
    NormExponentialDomain μ (fun _ => 1) := by
  refine ⟨by fun_prop, ?_⟩
  intro m a
  simpa only [norm_one, one_mul] using
    integrable_norm_pow_exp_norm_of_all_exponential_moments hμ m a

lemma integrable_exp_norm_map_of_linear_growth {n m : ℕ} {μ : Measure (Space n)}
    (hμ : ∀ a : ℝ, Integrable (fun x => Real.exp (a * ‖x‖)) μ)
    {G : Space n → Space m} (hG : Measurable G) {A B : ℝ}
    (hbound : ∀ x, ‖G x‖ ≤ A + B * ‖x‖) (a : ℝ) :
    Integrable (fun y => Real.exp (a * ‖y‖)) (μ.map G) := by
  apply (integrable_map_measure (by fun_prop) hG.aemeasurable).2
  apply ((hμ (|a| * B)).const_mul (Real.exp (|a| * A))).mono'
    (((hG.norm.const_mul a).exp).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖Real.exp (a * ‖G x‖)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    a * ‖G x‖ ≤ |a| * ‖G x‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    _ ≤ |a| * (A + B * ‖x‖) := mul_le_mul_of_nonneg_left (hbound x) (abs_nonneg _)
    _ = _ := by ring

lemma normExponentialDomain_one_map_of_linear_growth {n m : ℕ}
    {μ : Measure (Space n)}
    (hμ : NormExponentialDomain μ (fun _ => 1))
    {G : Space n → Space m} (hG : Measurable G) {A B : ℝ}
    (hbound : ∀ x, ‖G x‖ ≤ A + B * ‖x‖) :
    NormExponentialDomain (μ.map G) (fun _ => 1) := by
  apply normExponentialDomain_one_of_all_exponential_moments
  apply integrable_exp_norm_map_of_linear_growth (G := G) _ hG hbound
  intro a
  simpa only [norm_one, pow_zero, one_mul] using hμ.2 0 a

/-- Literal graph coordinates: the first coordinate is the signal, followed
by the original coordinates. -/
def suspensionGraph {n : ℕ} (f : Space n → ℝ) (x : Space n) : Space (n + 1) :=
  WithLp.toLp 2 (Fin.cons (f x) (fun j => x j))

lemma measurable_suspensionGraph {n : ℕ} {f : Space n → ℝ} (hf : Measurable f) :
    Measurable (suspensionGraph f) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).measurable.comp
  apply Measurable.of_eval
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using hf
  · simpa only [Fin.cons_succ] using (show Measurable (fun x : Space n => x j) by fun_prop)

lemma norm_suspensionGraph_le {n : ℕ} (f : Space n → ℝ) (x : Space n) :
    ‖suspensionGraph f x‖ ≤ |f x| + ‖x‖ := by
  have he : ‖suspensionGraph f x‖ ^ 2 = (f x) ^ 2 + ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, EuclideanSpace.real_norm_sq_eq]
    rfl
  nlinarith [norm_nonneg (suspensionGraph f x), abs_nonneg (f x), norm_nonneg x,
    mul_nonneg (abs_nonneg (f x)) (norm_nonneg x), sq_abs (f x)]

lemma normExponentialDomain_suspensionGraph {n : ℕ} {μ : Measure (Space n)}
    (hμ : NormExponentialDomain μ (fun _ => 1)) {f : Space n → ℝ}
    (hf : Measurable f) {A B : ℝ} (hbound : ∀ x, |f x| ≤ A + B * ‖x‖) :
    NormExponentialDomain (μ.map (suspensionGraph f)) (fun _ => 1) := by
  apply normExponentialDomain_one_map_of_linear_growth hμ (measurable_suspensionGraph hf)
    (A := A) (B := B + 1)
  intro x
  calc
    ‖suspensionGraph f x‖ ≤ |f x| + ‖x‖ := norm_suspensionGraph_le f x
    _ ≤ (A + B * ‖x‖) + ‖x‖ := by linarith [hbound x]
    _ = A + (B + 1) * ‖x‖ := by ring

end KLS
end
#print axioms KLS.normExponentialDomain_suspensionGraph
