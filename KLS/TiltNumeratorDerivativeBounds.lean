import KLS.TiltNumeratorMoments

/-! Genuine numerator derivative bounds. The constants may depend on the
dimension, order and law; they are used only to establish L2 continuity. -/

open MeasureTheory Filter Matrix
open scoped ENNReal ContDiff BigOperators
noncomputable section
namespace KLS

lemma norm_inner_product_le {n d : ℕ} (x : Space n) (m : Fin d → Space n) :
    ‖∏ j, inner ℝ x (m j)‖ ≤ ‖x‖ ^ d * ∏ j, ‖m j‖ := by
  rw [norm_prod]
  calc
    _ ≤ ∏ j, (‖x‖ * ‖m j‖) := Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
      (fun j _ => norm_inner_le_norm (𝕜 := ℝ) x (m j))
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem norm_iteratedFDeriv_tiltNumerator_le_moment {n d : ℕ} {μ : Measure (Space n)}
    {f : Space n → ℝ} (hf : NormExponentialDomain μ f) :
    ‖iteratedFDeriv ℝ d (tiltNumerator μ (fun _ => 0) f) 0‖ ≤
      ∫ x, ‖f x‖ * ‖x‖ ^ d ∂μ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (integral_nonneg (fun _ => by positivity))
  intro m
  rw [iteratedFDeriv_tiltNumerator_moment hf]
  simp only [inner_zero_left, Real.exp_zero, mul_one]
  have hi : Integrable (fun x => f x * ∏ j, inner ℝ x (m j)) μ := by
    simpa only [innerWordMonomial, List.map_ofFn, List.prod_ofFn, Function.comp_apply,
      inner_zero_left, Real.exp_zero, mul_one] using
      (hf.mul_innerWord (List.ofFn m)).integrable_tilt 0
  have hbound : Integrable (fun x => (‖f x‖ * ‖x‖ ^ d) * ∏ j, ‖m j‖) μ := by
    apply Integrable.mul_const
    simpa only [zero_mul, Real.exp_zero, mul_one] using hf.2 d 0
  calc
    _ ≤ ∫ x, ‖f x * ∏ j, inner ℝ x (m j)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (‖f x‖ * ‖x‖ ^ d) * ∏ j, ‖m j‖ ∂μ :=
      integral_mono_ae hi.norm hbound (Eventually.of_forall (fun x => by
        dsimp only
        rw [norm_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left (norm_inner_product_le x m) (norm_nonneg _)))
    _ = _ := integral_mul_const _ _

lemma integral_norm_mul_le_L2Norm {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ 2 μ) {g : α → ℝ} (hg : MemLp g 2 μ) :
    (∫ x, ‖f x‖ * g x ∂μ) ≤ ‖f‖ * ‖hg.toLp g‖ := by
  let F := (Lp.memLp f).norm.toLp (fun x => ‖f x‖)
  let G := hg.toLp g
  have he : (∫ x, ‖f x‖ * g x ∂μ) = inner ℝ F G := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(Lp.memLp f).norm.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    change ‖f x‖ * g x = inner ℝ (F x) (G x)
    rw [show F x = ‖f x‖ from hx, show G x = g x from hy]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hn : ‖F‖ = ‖f‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable f), Lp.norm_def]
  rw [he]
  simpa only [hn] using real_inner_le_norm F G

theorem exists_tiltNumerator_derivative_L2_bound {n : ℕ} {V : Space n → ℝ} {κ : ℝ}
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Lp ℝ 2 (potentialMeasure V),
      ‖iteratedFDeriv ℝ d (tiltNumerator (potentialMeasure V) (fun _ => 0) f) 0‖ ≤ C * ‖f‖ := by
  have hg : MemLp (fun x : Space n => ‖x‖ ^ d) 2 (potentialMeasure V) := by
    simpa using memLp_norm_pow_mul_exp_norm_potentialMeasure hV hκ hlower d 0
  refine ⟨‖hg.toLp (fun x => ‖x‖ ^ d)‖, norm_nonneg _, ?_⟩
  intro f
  calc
    _ ≤ ∫ x, ‖f x‖ * ‖x‖ ^ d ∂potentialMeasure V :=
      norm_iteratedFDeriv_tiltNumerator_le_moment
        (normExponentialDomain_of_memLp_potentialMeasure hV hκ hlower (Lp.memLp f))
    _ ≤ ‖f‖ * ‖hg.toLp (fun x => ‖x‖ ^ d)‖ := integral_norm_mul_le_L2Norm f hg
    _ = _ := mul_comm _ _

end KLS
end
#print axioms KLS.exists_tiltNumerator_derivative_L2_bound
