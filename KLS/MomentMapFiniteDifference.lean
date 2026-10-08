import KLS.ConvexPotentialCoercivity
import KLS.ConvexHessian
import KLS.LocalRademacher
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor

/-!
# Actual finite differences and coercive penalized maxima

Bounded gradient controls actual second differences. Subtracting a positive
multiple of the genuine source potential then yields an attained global
maximum, using the already proved compactness of finite-mass convex sublevels.
No Hessian bound or maximum-attainment hypothesis is used.
-/

open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ContDiff NNReal
noncomputable section
namespace KLS

variable {n : ℕ}

def symmetricSecondDifference (φ : Space n → ℝ) (h x : Space n) : ℝ :=
  φ (x + h) + φ (x - h) - 2 * φ x

lemma symmetricSecondDifference_contDiff {φ : Space n → ℝ} {m : ℕ∞}
    (hφ : ContDiff ℝ m φ) (h : Space n) :
    ContDiff ℝ m (symmetricSecondDifference φ h) := by
  unfold symmetricSecondDifference
  fun_prop

lemma symmetricSecondDifference_nonneg {φ : Space n → ℝ}
    (hφ : ConvexOn ℝ univ φ) (h x : Space n) :
    0 ≤ symmetricSecondDifference φ h x := by
  have hh := hφ.2 (mem_univ (x + h)) (mem_univ (x - h))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have he : (1 / 2 : ℝ) • (x + h) + (1 / 2 : ℝ) • (x - h) = x := by module
  rw [he] at hh
  simp only [smul_eq_mul] at hh
  unfold symmetricSecondDifference
  linarith

lemma symmetricSecondDifference_le_of_lipschitz {φ : Space n → ℝ} {R : ℝ≥0}
    (hφ : LipschitzWith R φ) (h x : Space n) :
    symmetricSecondDifference φ h x ≤ 2 * (R : ℝ) * ‖h‖ := by
  have hp := hφ.norm_sub_le (x + h) x
  have hm := hφ.norm_sub_le (x - h) x
  simp only [add_sub_cancel_left, sub_sub_cancel_left, norm_neg, Real.norm_eq_abs] at hp hm
  have hp' := (le_abs_self (φ (x + h) - φ x)).trans hp
  have hm' := (le_abs_self (φ (x - h) - φ x)).trans hm
  unfold symmetricSecondDifference
  linarith

lemma lipschitzWith_of_bounded_gradient {φ : Space n → ℝ}
    (hφ : Differentiable ℝ φ) (hb : Bornology.IsBounded (range (gradient φ))) :
    ∃ R : ℝ≥0, LipschitzWith R φ := by
  obtain ⟨R, hR⟩ := hb.exists_norm_le
  have hR' : 0 ≤ R := (norm_nonneg (gradient φ 0)).trans (hR _ (mem_range_self 0))
  refine ⟨⟨R, hR'⟩, lipschitzWith_of_nnnorm_fderiv_le hφ (fun x => ?_)⟩
  change ‖fderiv ℝ φ x‖ ≤ R
  rw [← norm_gradient_eq_norm_fderiv]
  exact hR _ (mem_range_self x)

/-- The actual penalized second difference attains its maximum on the whole
space. This replaces an unjustified unpenalized maximum principle. -/
theorem exists_maximizer_penalizedSecondDifference {φ : Space n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ)
    [IsFiniteMeasure (potentialMeasure φ)] {R : ℝ≥0} (hR : LipschitzWith R φ)
    (h : Space n) {η : ℝ} (hη : 0 < η) :
    ∃ x₀ : Space n, ∀ x, symmetricSecondDifference φ h x - η * φ x ≤
      symmetricSecondDifference φ h x₀ - η * φ x₀ := by
  have hcont : Continuous (fun x => symmetricSecondDifference φ h x - η * φ x) := by
    unfold symmetricSecondDifference
    fun_prop
  apply hcont.exists_forall_ge
  apply tendsto_atBot.2
  intro b
  filter_upwards [(tendsto_potential_cocompact_atTop hφ hc).eventually
    (eventually_ge_atTop ((2 * (R : ℝ) * ‖h‖ - b) / η))] with x hx
  have hmul : 2 * (R : ℝ) * ‖h‖ - b ≤ η * φ x := by
    have hh := (div_le_iff₀ hη).mp hx
    linarith
  have hh := symmetricSecondDifference_le_of_lipschitz hR h x
  linarith

/-- A supporting-plane inequality proved from the actual derivative along
an affine line. -/
lemma convex_supporting_fderiv {φ : Space n → ℝ} (hc : ConvexOn ℝ univ φ)
    (hφ : Differentiable ℝ φ) (x y : Space n) :
    φ x + fderiv ℝ φ x (y - x) ≤ φ y := by
  have hd : HasDerivAt (fun t : ℝ => φ (x + t • (y - x)))
      (fderiv ℝ φ x (y - x)) 0 := by
    convert! (hφ (x + (0 : ℝ) • (y - x))).hasFDerivAt.comp_hasDerivAt 0
        (hasDerivAt_affine_line x (y - x) 0) using 1
    simp
  have hh := (convexOn_affine_line hc x (y - x)).le_slope_of_hasDerivAt
    (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) (by norm_num) hd
  simp only [slope_def_field, zero_smul, add_zero, one_smul, add_sub_cancel,
    sub_zero, div_one] at hh
  linarith

lemma symmetricSecondDifference_le_gradient_difference {φ : Space n → ℝ}
    (hc : ConvexOn ℝ univ φ) (hφ : Differentiable ℝ φ) (h x : Space n) :
    symmetricSecondDifference φ h x ≤
      inner ℝ (gradient φ (x + h) - gradient φ (x - h)) h := by
  have hp := convex_supporting_fderiv hc hφ (x + h) x
  have hm := convex_supporting_fderiv hc hφ (x - h) x
  have hep : x - (x + h) = -h := by abel
  have hem : x - (x - h) = h := by abel
  rw [hep, map_neg, ← inner_gradient_left] at hp
  rw [hem, ← inner_gradient_left] at hm
  rw [inner_sub_left]
  unfold symmetricSecondDifference
  linarith

lemma hasFDerivAt_symmetricSecondDifference {φ : Space n → ℝ}
    (hφ : Differentiable ℝ φ) (h x : Space n) :
    HasFDerivAt (symmetricSecondDifference φ h)
      (fderiv ℝ φ (x + h) + fderiv ℝ φ (x - h) - (2 : ℝ) • fderiv ℝ φ x) x := by
  have hp := (hφ (x + h)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const h)
  have hm := (hφ (x - h)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const h)
  convert! (hp.add hm).sub ((hφ x).hasFDerivAt.const_mul 2) using 1

lemma gradient_symmetricSecondDifference {φ : Space n → ℝ}
    (hφ : Differentiable ℝ φ) (h x : Space n) :
    gradient (symmetricSecondDifference φ h) x =
      gradient φ (x + h) + gradient φ (x - h) - (2 : ℝ) • gradient φ x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, (hasFDerivAt_symmetricSecondDifference hφ h x).fderiv]
  simp only [sub_apply, add_apply,
    smul_apply, inner_sub_left, inner_add_left, inner_smul_left,
    conj_trivial, inner_gradient_left, smul_eq_mul]

/-- At an actual penalized maximum, the gradient discrepancy is exactly the
penalty times the source gradient. -/
lemma gradient_symmetricSecondDifference_at_penalized_max {φ : Space n → ℝ}
    (hφ : Differentiable ℝ φ) (h : Space n) (η : ℝ) (x₀ : Space n)
    (hmax : ∀ x, symmetricSecondDifference φ h x - η * φ x ≤
      symmetricSecondDifference φ h x₀ - η * φ x₀) :
    gradient φ (x₀ + h) + gradient φ (x₀ - h) - (2 : ℝ) • gradient φ x₀ =
      η • gradient φ x₀ := by
  have hd := (hasFDerivAt_symmetricSecondDifference hφ h x₀).sub
    ((hφ x₀).hasFDerivAt.const_mul η)
  have hl : IsLocalMax (fun x => symmetricSecondDifference φ h x - η * φ x) x₀ :=
    Eventually.of_forall hmax
  have hh := hl.hasFDerivAt_eq_zero hd
  apply ext_inner_right ℝ
  intro v
  have hv := congrArg (fun F : Space n →L[ℝ] ℝ => F v) hh
  simp only [sub_apply, add_apply,
    smul_apply, zero_apply, smul_eq_mul] at hv
  simp only [inner_sub_left, inner_add_left, inner_smul_left, conj_trivial,
    inner_gradient_left]
  linarith

/-- The symmetric second difference converges to the genuine second
ordinary derivative; the deleted neighborhood avoids assigning meaning to
its zero denominator. -/
lemma tendsto_symmetricSecondDifference_real {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) :
    Tendsto (fun t : ℝ => (F t + F (-t) - 2 * F 0) / t ^ 2)
      (𝓝[≠] 0) (𝓝 (deriv (deriv F) 0)) := by
  have ht : Tendsto
      (fun t : ℝ => (F t - (F 0 + t * deriv F 0 + (t ^ 2 / 2) * deriv (deriv F) 0)) / t ^ 2)
      (𝓝 0) (𝓝 0) := by
    have hh := Real.taylor_tendsto (f := F) (n := 2) convex_univ (mem_univ (0 : ℝ))
      hF.contDiffOn
    convert hh using 1 <;>
      norm_num [taylorWithinEval_succ, iteratedDerivWithin_univ, iteratedDeriv_succ,
        Nat.factorial, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg : Continuous (fun t : ℝ => -t)).tendsto 0
  have hh := (ht.add (ht.comp hneg)).add_const (deriv (deriv F) 0)
  have hh' : Tendsto
      (fun t : ℝ =>
        (F t - (F 0 + t * deriv F 0 + (t ^ 2 / 2) * deriv (deriv F) 0)) / t ^ 2 +
        (F (-t) - (F 0 + (-t) * deriv F 0 + ((-t) ^ 2 / 2) * deriv (deriv F) 0)) / (-t) ^ 2 +
        deriv (deriv F) 0)
      (𝓝[≠] 0) (𝓝 (deriv (deriv F) 0)) := by
    simpa only [zero_add, Function.comp_def] using hh.mono_left nhdsWithin_le_nhds
  apply hh'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  field_simp
  ring


lemma deriv_deriv_affine_line_eq {F : Space n → ℝ}
    (hF : ContDiff ℝ 2 F) (x v : Space n) :
    deriv (deriv (fun t : ℝ => F (x + t • v))) 0 =
      fderiv ℝ (fderiv ℝ F) x v v := by
  have hdF : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hddF : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  let G : ℝ → ℝ := fun t => F (x + t • v)
  have hd (t : ℝ) : HasDerivAt G (fderiv ℝ F (x + t • v) v) t :=
    (hdF (x + t • v)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_affine_line x v t)
  have hder : deriv G = fun t => fderiv ℝ F (x + t • v) v := by
    funext t
    exact (hd t).deriv
  have hdmap := (hddF (x + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_affine_line x v 0)
  have hdmap' : HasDerivAt (fun t : ℝ => fderiv ℝ F (x + t • v))
      (fderiv ℝ (fderiv ℝ F) x v) 0 := by
    convert! hdmap using 1
    simp
  have hdeval := hdmap'.clm_apply (hasDerivAt_const (0 : ℝ) v)
  change deriv (deriv G) 0 = _
  rw [hder]
  simpa using hdeval.deriv

lemma tendsto_symmetricSecondDifference_directional {F : Space n → ℝ}
    (hF : ContDiff ℝ 2 F) (x v : Space n) :
    Tendsto (fun t : ℝ => symmetricSecondDifference F (t • v) x / t ^ 2)
      (𝓝[≠] 0) (𝓝 (fderiv ℝ (fderiv ℝ F) x v v)) := by
  have hG : ContDiff ℝ 2 (fun t : ℝ => F (x + t • v)) := by fun_prop
  have hh := tendsto_symmetricSecondDifference_real hG
  rw [deriv_deriv_affine_line_eq hF] at hh
  simpa only [symmetricSecondDifference, neg_smul, ← sub_eq_add_neg, zero_smul, add_zero] using hh

lemma secondFrechet_nonpos_at_global_max {F : Space n → ℝ}
    (hF : ContDiff ℝ 2 F) (x : Space n) (hmax : ∀ y, F y ≤ F x) (v : Space n) :
    fderiv ℝ (fderiv ℝ F) x v v ≤ 0 := by
  apply le_of_tendsto (tendsto_symmetricSecondDifference_directional hF x v)
  apply Eventually.of_forall
  intro t
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg t)
  have hp := hmax (x + t • v)
  have hm := hmax (x - t • v)
  unfold symmetricSecondDifference
  linarith

end KLS
end

#print axioms KLS.exists_maximizer_penalizedSecondDifference
#print axioms KLS.gradient_symmetricSecondDifference_at_penalized_max
#print axioms KLS.tendsto_symmetricSecondDifference_directional
#print axioms KLS.secondFrechet_nonpos_at_global_max
