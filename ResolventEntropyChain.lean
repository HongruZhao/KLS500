import KLS.HessianMetricComposition
import KLS.SmoothSignGradient
import KLS.WeightedResolventVariance

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS.ConstantReduction
variable {n : ℕ}

theorem weightedDiffusion_scalar_comp (φ : Space n → ℝ)
    {η : ℝ → ℝ} {u : Space n → ℝ}
    (hη : ContDiff ℝ 2 η) (hu : ContDiff ℝ 2 u) (x : Space n) :
    weightedDiffusion φ (fun y => η (u y)) x =
      deriv η (u x) * weightedDiffusion φ u x +
        deriv (deriv η) (u x) * ‖gradient u x‖^2 := by
  rw [weightedDiffusion_eq_sum,weightedDiffusion_eq_sum]
  simp_rw [coordinateHessian_scalar_comp hη hu,
    coordinateDerivative_scalar_comp (hη.differentiable (by norm_num) _)
      (hu.differentiable (by norm_num) _)]
  rw [← real_inner_self_eq_norm_sq, ← sum_coordinateDerivative_mul]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Concavity and the scalar entropy curvature yield an actual resolvent
supersolution for the squared gradient divided by the positive entropy. -/
theorem entropy_resolvent_supersolution {φ u f : Space n → ℝ} {η : ℝ → ℝ}
    (hη : ContDiff ℝ 2 η) (hu : ContDiff ℝ 2 u) {t : ℝ} (ht : 0 ≤ t)
    (heq : ∀ x, u x-t*weightedDiffusion φ u x=f x)
    (hpos : ∀ x, 0 < η (u x))
    (hconc : ∀ x, η (f x) ≤ η (u x)+deriv η (u x)*(f x-u x))
    (hcurv : ∀ x, 1 ≤ η (u x)*(-deriv (deriv η) (u x))) :
    ∀ x, η (f x)+t*(‖gradient u x‖^2/η (u x)) ≤
      η (u x)-t*weightedDiffusion φ (fun y => η (u y)) x := by
  intro x
  have hc : ‖gradient u x‖^2/η (u x) ≤
      (-deriv (deriv η) (u x))*‖gradient u x‖^2 := by
    apply (div_le_iff₀ (hpos x)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right (hcurv x) (sq_nonneg ‖gradient u x‖)]
  have hh := mul_le_mul_of_nonneg_left hc ht
  rw [weightedDiffusion_scalar_comp φ hη hu]
  have hd := congrArg (fun z => deriv η (u x)*z) (heq x)
  nlinarith only [hconc x, hh, hd]

/-- Actual smooth solutions for the two entropy forcing terms lie below the
entropy of the actual resolvent output. All comparison integrability is explicit. -/
theorem entropy_resolvent_comparison {φ u f v w : Space n → ℝ} {η : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hηu : ContDiff ℝ 3 (fun x => η (u x)))
    (hv : ContDiff ℝ 3 v) (hw : ContDiff ℝ 3 w) {t : ℝ} (ht : 0 < t)
    (hsuper : ∀ x, η (f x)+t*(‖gradient u x‖^2/η (u x)) ≤
      η (u x)-t*weightedDiffusion φ (fun y => η (u y)) x)
    (hev : ∀ x, v x-t*weightedDiffusion φ v x=η (f x))
    (hew : ∀ x, w x-t*weightedDiffusion φ w x=‖gradient u x‖^2/η (u x))
    (hIη : Integrable (fun x => η (u x)) (potentialMeasure φ))
    (hIv : Integrable v (potentialMeasure φ)) (hIw : Integrable w (potentialMeasure φ))
    (hgη : Integrable (gradient (fun x => η (u x))) (potentialMeasure φ))
    (hgv : Integrable (gradient v) (potentialMeasure φ))
    (hgw : Integrable (gradient w) (potentialMeasure φ)) :
    ∀ x, v x+t*w x ≤ η (u x) := by
  let z : Space n → ℝ := (v+t • w)+(-1 : ℝ) • (fun x => η (u x))
  have hz : ContDiff ℝ 3 z :=
    (hv.add (hw.const_smul t)).add (hηu.const_smul (-1 : ℝ))
  have hIz : Integrable z (potentialMeasure φ) :=
    (hIv.add (hIw.smul t)).add (hIη.smul (-1 : ℝ))
  have hgrad : gradient z = (gradient v+t • gradient w)+
      (-1 : ℝ) • gradient (fun x => η (u x)) := by
    funext x
    dsimp only [z]
    rw [gradient_add_real ((hv.differentiable (by norm_num) x).add
      ((hw.differentiable (by norm_num) x).const_smul t))
      ((hηu.differentiable (by norm_num) x).const_smul (-1 : ℝ)),
      gradient_add_real (hv.differentiable (by norm_num) x)
        ((hw.differentiable (by norm_num) x).const_smul t),
      gradient_smul_real (hw.differentiable (by norm_num) x),
      gradient_smul_real (hηu.differentiable (by norm_num) x)]
    rfl
  have hGz : Integrable (gradient z) (potentialMeasure φ) := by
    rw [hgrad]
    exact (hgv.add (hgw.smul t)).add (hgη.smul (-1 : ℝ))
  have hsub (x : Space n) : z x-t*weightedDiffusion φ z x ≤ 0 := by
    have hL : weightedDiffusion φ z x = weightedDiffusion φ v x+
        t*weightedDiffusion φ w x+(-1 : ℝ)*weightedDiffusion φ (fun y => η (u y)) x := by
      dsimp only [z]
      rw [weightedDiffusion_add (f := v+t • w) (g := (-1:ℝ) • (fun x => η (u x))) ((hv.add (hw.const_smul t)).of_le (by norm_num))
        ((hηu.const_smul (-1 : ℝ)).of_le (by norm_num)),
        weightedDiffusion_add (f := v) (g := t • w) (hv.of_le (by norm_num)) ((hw.const_smul t).of_le (by norm_num)),
        weightedDiffusion_smul (hw.of_le (by norm_num)),weightedDiffusion_smul (hηu.of_le (by norm_num))]
    rw [hL]
    dsimp only [z,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    have hwt := congrArg (fun a => t*a) (hew x)
    nlinarith only [hsuper x,hev x,hwt]
  have hmax := nonpos_of_weighted_resolvent_subsolution hφ hz ht hsub hIz hGz.norm
  intro x
  have hx := hmax x
  change v x+t*w x+(-1:ℝ)*η (u x) ≤ 0 at hx
  linarith

/-- The genuine resolvent constructs the entropy and weighted-gradient pair.
Every L2 input and every comparison integrability condition follows from the
stated bounded profile and actual bounded gradient. -/
theorem weightedMassResolvent_exists_entropy_pair
    {φ u f : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {η : ℝ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {t m H D M : ℝ} (ht : 0 < t) (hm : 0 < m)
    (hD : 0 ≤ D) (hM : 0 ≤ M)
    (heq : ∀ x, u x-t*weightedDiffusion φ u x=f x)
    (hηf : ∀ x, |η (f x)| ≤ H) (hηu : ∀ x, |η (u x)| ≤ H)
    (hmlow : ∀ x, m ≤ η (u x))
    (hderiv : ∀ x, |deriv η (u x)| ≤ D)
    (hgrad : ∀ x, ‖gradient u x‖ ≤ M)
    (hconc : ∀ x, η (f x) ≤ η (u x)+deriv η (u x)*(f x-u x))
    (hcurv : ∀ x, 1 ≤ η (u x)*(-deriv (deriv η) (u x))) :
    ∃ hF2 : MemLp (fun x => η (f x)) 2 (potentialMeasure φ),
    ∃ hQ2 : MemLp (fun x => ‖gradient u x‖^2/η (u x)) 2 (potentialMeasure φ),
    ∃ v w : Space n → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) v ∧ ContDiff ℝ (⊤ : ℕ∞) w ∧
      MemLp v 2 (potentialMeasure φ) ∧ MemLp w 2 (potentialMeasure φ) ∧
      v =ᵐ[potentialMeasure φ] (weightedMassResolvent φ ht (hF2.toLp (fun x => η (f x))) : Space n → ℝ) ∧
      w =ᵐ[potentialMeasure φ] (weightedMassResolvent φ ht (hQ2.toLp (fun x => ‖gradient u x‖^2/η (u x))) : Space n → ℝ) ∧
      (∀ x, v x-t*weightedDiffusion φ v x=η (f x)) ∧
      (∀ x, w x-t*weightedDiffusion φ w x=‖gradient u x‖^2/η (u x)) ∧
      (∀ x, 0 ≤ w x) ∧ (∀ x, v x+t*w x ≤ η (u x)) ∧
      (∀ x, v x ≤ η (u x)) := by
  have hpos (x : Space n) : 0 < η (u x) := hm.trans_le (hmlow x)
  have hηfu : ContDiff ℝ (⊤ : ℕ∞) (fun x => η (f x)) := hη.comp hf
  have hηuu : ContDiff ℝ (⊤ : ℕ∞) (fun x => η (u x)) := hη.comp hu
  have hF2 : MemLp (fun x => η (f x)) 2 (potentialMeasure φ) := by
    apply MemLp.of_bound hηfu.continuous.aestronglyMeasurable H
    exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hηf x
  have hηu2 : MemLp (fun x => η (u x)) 2 (potentialMeasure φ) := by
    apply MemLp.of_bound hηuu.continuous.aestronglyMeasurable H
    exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hηu x
  have hQ : ContDiff ℝ (⊤ : ℕ∞) (fun x => ‖gradient u x‖^2/η (u x)) :=
    (contDiff_gradient_norm_sq hu (by simp)).div hηuu (fun x => (hpos x).ne')
  have hQ2 : MemLp (fun x => ‖gradient u x‖^2/η (u x)) 2 (potentialMeasure φ) := by
    apply MemLp.of_bound hQ.continuous.aestronglyMeasurable (M^2/m)
    apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) (hpos x).le)]
    calc
      _ ≤ M^2/η (u x) := div_le_div_of_nonneg_right
        ((sq_le_sq₀ (norm_nonneg _) hM).mpr (hgrad x)) (hpos x).le
      _ ≤ M^2/m := div_le_div_of_nonneg_left (sq_nonneg _) hm (hmlow x)
  have hGη : MemLp (gradient (fun x => η (u x))) 2 (potentialMeasure φ) := by
    apply MemLp.of_bound
      (continuous_gradient_of_contDiff (hηuu.of_le (by simp))).aestronglyMeasurable (D*M)
    apply Eventually.of_forall
    intro x
    rw [gradient_scalar_comp_real (hη.differentiable (by simp) _)
      (hu.differentiable (by simp) _),norm_smul,Real.norm_eq_abs]
    exact mul_le_mul (hderiv x) (hgrad x) (norm_nonneg _) hD
  obtain ⟨v,hv,hv2,hdv,_,hvμ,_,hev⟩ :=
    weightedMassResolvent_exists_smooth_representative hφ ht hηfu hF2
  obtain ⟨w,hw,hw2,hdw,_,hwμ,_,hew⟩ :=
    weightedMassResolvent_exists_smooth_representative hφ ht hQ hQ2
  have hgv := (memLp_gradient_of_coordinateDerivative (hv.of_le (by simp)) hdv).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hgw := (memLp_gradient_of_coordinateDerivative (hw.of_le (by simp)) hdw).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hsuper := entropy_resolvent_supersolution (hη.of_le (by simp)) (hu.of_le (by simp))
    ht.le heq hpos hconc hcurv
  have hbound := entropy_resolvent_comparison (hφ.of_le (by simp)) (hηuu.of_le (by simp))
    (hv.of_le (by simp)) (hw.of_le (by simp)) ht hsuper hev hew
    (hηu2.integrable (by norm_num)) (hv2.integrable (by norm_num)) (hw2.integrable (by norm_num))
    (hGη.integrable (by norm_num)) hgv hgw
  have hw0 : ∀ x, 0 ≤ w x := by
    apply weightedMassResolvent_lower_bound_of_representative (hφ.of_le (by simp)) ht
      (hQ2.toLp (fun x => ‖gradient u x‖^2/η (u x))) (hw.of_le (by simp)) hwμ
    filter_upwards [hQ2.coeFn_toLp] with x hx
    rw [hx]
    exact div_nonneg (sq_nonneg _) (hpos x).le
  refine ⟨hF2,hQ2,v,w,hv,hw,hv2,hw2,hvμ,hwμ,hev,hew,hw0,hbound,?_⟩
  intro x
  have hh := hbound x
  have hp := mul_nonneg ht.le (hw0 x)
  linarith

end KLS.ConstantReduction
end
