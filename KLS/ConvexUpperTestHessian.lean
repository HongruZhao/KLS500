import KLS.SymmetricQuadraticCalculus
import KLS.SemidefiniteTestViscosity

/-! Convexity forces every genuine local C2 upper test to have a positive
semidefinite Hessian. Thus the upper viscosity inequality needs no separately
assumed sign condition on the test Hessian. -/

open MeasureTheory InnerProductSpace Matrix Set Filter
open scoped Topology ENNReal NNReal ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

lemma centeredQuadratic_central_sum (A : Matrix (Fin n) (Fin n) ℝ)
    (x₀ p : Space n) (c : ℝ) (h : Space n) :
    centeredQuadratic A x₀ p c (x₀ + h) + centeredQuadratic A x₀ p c (x₀ - h) - 2 * c =
      inner ℝ h (matrixAction A h) := by
  simp only [centeredQuadratic, add_sub_cancel_left,
    show x₀ - h - x₀ = -h by abel, map_neg, inner_neg_left, inner_neg_right]
  ring

lemma inner_hessian_nonneg_of_convex_upper_touch
    {u ψ : Space n → ℝ} (huc : ConvexOn ℝ univ u) {x₀ : Space n}
    (hψ : ContDiffAt ℝ 2 ψ x₀) (hcontact : u x₀ = ψ x₀)
    (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x) (v : Space n) :
    0 ≤ inner ℝ v (matrixAction (coordinateHessian ψ x₀) v) := by
  by_contra hnot
  let A := coordinateHessian ψ x₀
  let H := inner ℝ v (matrixAction A v)
  have hH : H < 0 := lt_of_not_ge hnot
  have hecont : Continuous (fun ε : ℝ => H + 2 * ε * ‖v‖ ^ 2) := by fun_prop
  have hevent : ∀ᶠ ε in 𝓝 (0 : ℝ), H + 2 * ε * ‖v‖ ^ 2 < 0 :=
    hecont.continuousAt.eventually (Iio_mem_nhds (by simpa using hH))
  obtain ⟨ε, hε, _, hneg⟩ := exists_pos_lt_of_eventually_zero zero_lt_one hevent
  have htaylor := eventually_abs_sub_quadratic_taylor_le_sq hψ hε
  have hpluscont : Tendsto (fun t : ℝ => x₀ + t • v) (𝓝 0) (𝓝 x₀) := by
    have hh : Continuous (fun t : ℝ => x₀ + t • v) := by fun_prop
    simpa using hh.tendsto (0 : ℝ)
  have hminuscont : Tendsto (fun t : ℝ => x₀ - t • v) (𝓝 0) (𝓝 x₀) := by
    have hh : Continuous (fun t : ℝ => x₀ - t • v) := by fun_prop
    simpa using hh.tendsto (0 : ℝ)
  obtain ⟨t, ht, _, hp, hm⟩ := exists_pos_lt_of_eventually_zero zero_lt_one
    ((hpluscont.eventually (htouch.and htaylor)).and (hminuscont.eventually (htouch.and htaylor)))
  have hmid := symmetricSecondDifference_nonneg huc (t • v) x₀
  rw [symmetricSecondDifference, hcontact] at hmid
  have hψmid : 0 ≤ ψ (x₀ + t • v) + ψ (x₀ - t • v) - 2 * ψ x₀ := by
    linarith [hp.1, hm.1]
  have hpbound := (abs_le.mp hp.2).2
  have hmbound := (abs_le.mp hm.2).2
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_pow] at hpbound
  simp only [show x₀ - t • v - x₀ = -(t • v) by abel, norm_neg, norm_smul,
    Real.norm_eq_abs, abs_of_pos ht, mul_pow] at hmbound
  have hsum := centeredQuadratic_central_sum A x₀ (gradient ψ x₀) (ψ x₀) (t • v)
  simp only [map_smul, inner_smul_left, inner_smul_right, conj_trivial] at hsum
  change _ = t * (t * H) at hsum
  have hnegmul : t ^ 2 * (H + 2 * ε * ‖v‖ ^ 2) < 0 :=
    mul_neg_of_pos_of_neg (sq_pos_of_pos ht) hneg
  change ψ (x₀ + t • v) - centeredQuadratic A x₀ (gradient ψ x₀) (ψ x₀) (x₀ + t • v) ≤ _ at hpbound
  change ψ (x₀ - t • v) - centeredQuadratic A x₀ (gradient ψ x₀) (ψ x₀) (x₀ - t • v) ≤ _ at hmbound
  nlinarith

/-- The PSD sign of an upper test is derived from convexity of the weak
solution, without any differentiability assumption on that solution. -/
theorem coordinateHessian_posSemidef_of_convex_upper_touch
    {u ψ : Space n → ℝ} (huc : ConvexOn ℝ univ u) {x₀ : Space n}
    (hψ : ContDiffAt ℝ 2 ψ x₀) (hcontact : u x₀ = ψ x₀)
    (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x) :
    (coordinateHessian ψ x₀).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.isHermitian_iff_isSymm.mpr (coordinateHessian_isSymm_of_contDiffAt hψ)
  intro w
  have h := inner_hessian_nonneg_of_convex_upper_touch huc hψ hcontact htouch (WithLp.toLp 2 w)
  simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    dotProduct, Matrix.mulVec, matrixAction_apply, star_trivial, mul_comm] using h

/-- The unrestricted upper C2-test inequality for a convex Alexandrov solution. -/
theorem det_ge_density_of_convex_c2_upper_touch
    {u f ψ : Space n → ℝ} (hu : Continuous u) (huc : ConvexOn ℝ univ u) {x₀ : Space n}
    (hf : ContinuousAt f x₀)
    (hMA : ∀ S : Set (Space n), IsOpen S →
      volume (convexSubgradientImage u S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂volume)
    (hψ : ContDiffAt ℝ 2 ψ x₀)
    (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x) :
    f x₀ ≤ (coordinateHessian ψ x₀).det :=
  det_ge_density_of_c2_semidefinite_upper_touch hu hf hMA hψ
    (coordinateHessian_posSemidef_of_convex_upper_touch huc hψ hcontact htouch) hcontact htouch

end KLS
end

#print axioms KLS.coordinateHessian_posSemidef_of_convex_upper_touch
#print axioms KLS.det_ge_density_of_convex_c2_upper_touch
