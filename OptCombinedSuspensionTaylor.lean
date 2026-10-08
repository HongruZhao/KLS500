import OptCombinedSuspensionCumulant
import KLS.SuspensionCumulantTaylorBound

/-! Restricting the genuine cumulant tensor to its disjoint pure-copy
blocks bounds the full affine-plus-signal Taylor vector at once. -/
open MeasureTheory Set Filter Matrix
open scoped ENNReal ContDiff Topology BigOperators
noncomputable section
namespace KLS
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

lemma suspension_combined_Taylor_sum_le_directionalCumulant {n N d : ℕ} {V f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure V)] (hV : ContDiff ℝ 2 V)
    (hμ : IsIsotropic (potentialMeasure V)) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hf : MemLp f 2 (potentialMeasure V)) (hfm : Measurable f) {A B : ℝ}
    (hbound : ∀ x, |f x| ≤ A + B * ‖x‖)
    (hmean : (∫ x, f x ∂potentialMeasure V) = 0)
    {β σ : ℝ} (hβ : 0 < β) (hσ : σ ≠ 0) (hN : 0 < N) (hd : 0 < d)
    (ρ : ℝ) (u : Space n) :
    (d.factorial : ℝ)^2 *
      (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V (fun x => ρ*f x + inner ℝ x u) d a ^ 2) ≤
      directionalCumulantSquare (euclideanSuspensionLaw (N := N) (potentialMeasure V)
        f β σ (Real.sqrt N)⁻¹) d (suspensionCombinedDirection n N (ρ*σ) u) := by
  let ν := euclideanSuspensionLaw (N := N) (potentialMeasure V) f β σ (Real.sqrt N)⁻¹
  let T : (Fin d → SuspensionIndex n N) → ℝ := fun a => cumulantTensor ν (d+1)
    (Fin.snoc (fun j => EuclideanSpace.basisFun (Fin (suspensionDimension n N)) ℝ
      (Fintype.equivFin (SuspensionIndex n N) (a j))) (suspensionCombinedDirection n N (ρ*σ) u))
  have hentry (i : Fin N) (a : Fin d → Fin n) :
      T (pureSuspensionBlock (i,a)) = ((d.factorial : ℝ) / ((1 : ℝ)*Real.sqrt N)) *
        exponentialTiltCoordinateTaylor V (fun x => ρ*f x + inner ℝ x u) d a := by
    have hi := cumulantTensor_suspension_combined_Taylor hV hμ hκ hlower hf hfm hbound hmean hβ hσ hN
      ρ u i (fun j => EuclideanSpace.basisFun (Fin n) ℝ (a j))
    simp_rw [suspensionBlockEmbedding_basisFun] at hi
    simpa only [T, ν, pureSuspensionBlock, exponentialTiltCoordinateTaylor,
      EuclideanSpace.basisFun_apply, one_mul] using hi
  have hh := suspensionTensor_norm_bound hN hd T
    (exponentialTiltCoordinateTaylor V (fun x => ρ*f x + inner ℝ x u) d) (by norm_num : (1 : ℝ) ≠ 0) hentry
  have he : (∑ a, T a^2) = directionalCumulantSquare ν d (suspensionCombinedDirection n N (ρ*σ) u) := by
    unfold directionalCumulantSquare
    rw [← (Equiv.piCongrRight (fun _ : Fin d => Fintype.equivFin (SuspensionIndex n N))).sum_comp]
    rfl
  rw [he] at hh
  simpa only [one_pow, div_one] using hh

theorem Taylor_sum_le_of_universalCumulant_normalized_combined {n d : ℕ} {V f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure V)] (hV : ContDiff ℝ 2 V)
    (hμ : IsIsotropic (potentialMeasure V)) (hfC : ContDiff ℝ 2 f)
    (hf : MemLp f 2 (potentialMeasure V))
    (hmean : (∫ x, f x ∂potentialMeasure V) = 0)
    (hfsq : (∫ x, (f x)^2 ∂potentialMeasure V) = 1)
    (hforth : ∀ j : Fin n, (∫ x, x j * f x ∂potentialMeasure V) = 0)
    {κ M A B b : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hHess : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    (hgrowth : ∀ x, |f x| ≤ A + B * ‖x‖) (hd : 0 < d) (hb : 0 ≤ b)
    (hglobal : UniversalDirectionalCumulantBound d b) (ρ : ℝ) (u : Space n) :
    (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V (fun x => ρ*f x + inner ℝ x u) d a ^ 2) ≤
      (b / (d.factorial : ℝ)^2) * (ρ^2 + ‖u‖^2) := by
  have hfac : 0 < (d.factorial : ℝ)^2 := by positivity
  have hb' : 0 ≤ b / (d.factorial : ℝ)^2 := div_nonneg hb hfac.le
  apply le_of_all_laplace_variance_factors (mul_nonneg hb' (add_nonneg (sq_nonneg ρ) (sq_nonneg ‖u‖)))
  intro β hβ
  obtain ⟨N, hN, hν⟩ := exists_isKLSMeasure_euclideanSuspensionLaw hV hfC hμ hf
    hmean hfsq hforth hκ hlower hHess hβ
  let σ := suspensionNormalization β
  have hσ : 0 < σ := suspensionNormalization_pos β
  have hbound := hglobal (suspensionDimension n N) _ hν (suspensionCombinedDirection n N (ρ*σ) u)
  rw [suspensionCombinedDirection_norm_sq hN] at hbound
  have hlow := suspension_combined_Taylor_sum_le_directionalCumulant hV hμ hκ hlower hf
    hfC.continuous.measurable hgrowth hmean hβ hσ.ne' hN hd ρ u
  have hh := hlow.trans hbound
  have hh' : (∑ a : Fin d → Fin n,
      exponentialTiltCoordinateTaylor V (fun x => ρ*f x + inner ℝ x u) d a ^ 2) ≤
      (b / (d.factorial : ℝ)^2) * ((ρ*σ)^2 + ‖u‖^2) := by
    have ht : (∑ a : Fin d → Fin n,
        exponentialTiltCoordinateTaylor V (fun x => ρ*f x + inner ℝ x u) d a ^ 2) ≤
        b * ((ρ*σ)^2 + ‖u‖^2) / (d.factorial : ℝ)^2 :=
      (le_div_iff₀ hfac).mpr (by simpa only [mul_comm] using hh)
    convert ht using 1
    ring
  have hσsq : σ^2 = 1 + 2 / β^2 := Real.sq_sqrt (by positivity)
  have hw : (ρ*σ)^2 + ‖u‖^2 ≤ (1 + 2 / β^2) * (ρ^2 + ‖u‖^2) := by
    rw [mul_pow, hσsq]
    nlinarith [mul_nonneg (show 0 ≤ (2 : ℝ)/β^2 by positivity) (sq_nonneg ‖u‖)]
  calc
    _ ≤ (b / (d.factorial : ℝ)^2) * ((ρ*σ)^2 + ‖u‖^2) := hh'
    _ ≤ (b / (d.factorial : ℝ)^2) * ((1 + 2 / β^2) * (ρ^2 + ‖u‖^2)) :=
      mul_le_mul_of_nonneg_left hw hb'
    _ = _ := by ring

end KLS
end
