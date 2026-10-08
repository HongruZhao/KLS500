import KLS.WeightedSuccessorDomain
import KLS.WeightedSuccessorSmooth

/-! The actual normalized successor satisfies the sharp one-step Bochner decay
with a genuine orthogonal Hessian defect. Both the current Hessian graph and
the successor's classical representative are constructed from proved domains. -/

open MeasureTheory InnerProductSpace Matrix Filter
open scoped ContDiff RealInnerProductSpace ENNReal

noncomputable section
namespace KLS
variable {n : ℕ}

theorem weightedSuccessorForcing_ae_of_representative
    {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι) (f : ι → Space n → ℝ)
    (hf : ∀ i, ContDiff ℝ 1 (f i))
    (hv : ∀ i, f i =ᵐ[volume] (weightedH1Value φ (U i) : Space n → ℝ))
    (ki : Fin n × ι) :
    (weightedSuccessorForcing hφ hκ hlower U ki : Space n → ℝ)
      =ᵐ[potentialMeasure φ] fun x => weightedSuccessorScale hφ hκ hlower U *
        (coordinateDerivative (f ki.2) ki.1 x -
          ∫ y, coordinateDerivative (f ki.2) ki.1 y ∂potentialMeasure φ) := by
  have hd : coordinateDerivative (f ki.2) ki.1 =ᵐ[potentialMeasure φ]
      (weightedH1Derivative φ ki.1 (U ki.2) : Space n → ℝ) := (withDensity_absolutelyContinuous _ _).ae_eq
    (weightedH1_coordinateDerivative_of_representative (hφ.of_le (by norm_num)) (U ki.2)
      (hf ki.2) (hv ki.2) ki.1)
  have hi := integral_congr_ae hd
  have hc : (weightedFamilyCenteredGradient φ ι U ki : Space n → ℝ)
      =ᵐ[potentialMeasure φ] fun x => weightedH1Derivative φ ki.1 (U ki.2) x -
        ∫ y, weightedH1Derivative φ ki.1 (U ki.2) y ∂potentialMeasure φ := by
    rcases ki with ⟨k, i⟩
    rw [weightedFamilyCenteredGradient_apply]
    exact CenteredL2.center_ae (potentialMeasure φ) _
  filter_upwards [hd, hc, Lp.coeFn_smul (weightedSuccessorScale hφ hκ hlower U)
    (weightedFamilyCenteredGradient φ ι U ki)] with x hx hy hz
  change (weightedSuccessorScale hφ hκ hlower U • weightedFamilyCenteredGradient φ ι U ki) x = _
  rw [hz, Pi.smul_apply, smul_eq_mul, hy, ← hi, ← hx]

/-- BKL (37), (39), and (45)--(47), now for the actual graph successor and actual
classical functions. Only the current smooth diffusion domain is assumed;
Hessian L² regularity, orthogonality, and the next diffusion domain are derived. -/
theorem exists_weightedNormalizedSuccessor_bochner_step
    {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι) (f : ι → Space n → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hv : ∀ i, f i =ᵐ[volume] (weightedH1Value φ (U i) : Space n → ℝ))
    (hL : ∀ i, MemLp (weightedDiffusion φ (f i)) 2 (potentialMeasure φ)) :
    ∃ (fnext : (Fin n × ι) → Space n → ℝ) (W : WeightedH1Family φ (Fin n × ι)),
      (∀ ki, ContDiff ℝ (⊤ : ℕ∞) (fnext ki) ∧ MemLp (fnext ki) 2 (potentialMeasure φ) ∧
        (∫ x, fnext ki x ∂potentialMeasure φ) = 0 ∧
        fnext ki =ᵐ[volume] (weightedH1Value φ
          (weightedNormalizedSuccessor (hφ.of_le (by simp)) hκ hlower U ki) : Space n → ℝ) ∧
        (∀ x, weightedDiffusion φ (fnext ki) x =
          -(weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower U *
            (coordinateDerivative (f ki.2) ki.1 x -
              ∫ y, coordinateDerivative (f ki.2) ki.1 y ∂potentialMeasure φ))) ∧
        MemLp (weightedDiffusion φ (fnext ki)) 2 (potentialMeasure φ)) ∧
      weightedFamilyValue φ (Fin n × ι) W = weightedFamilyCenteredGradient φ ι U ∧
      (∀ j k i, (weightedH1Derivative φ j (W (k, i)) : Space n → ℝ)
        =ᵐ[potentialMeasure φ] fun x => coordinateHessian (f i) x j k) ∧
      inner ℝ (weightedFamilyGradient φ (Fin n × ι) W -
        weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower U • weightedFamilyGradient φ (Fin n × ι)
          (weightedNormalizedSuccessor (hφ.of_le (by simp)) hκ hlower U))
        (weightedFamilyGradient φ (Fin n × ι)
          (weightedNormalizedSuccessor (hφ.of_le (by simp)) hκ hlower U)) = 0 ∧
      (∑ i, ∫ x, hessianSquare (f i) x ∂potentialMeasure φ) =
        (∑ ki, ∫ x, weightedDiffusion φ (fnext ki) x ^ 2 ∂potentialMeasure φ) +
          weightedSuccessorHessianDefect (hφ.of_le (by simp)) hκ hlower U W ∧
      (∑ ki, ∫ x, weightedDiffusion φ (fnext ki) x ^ 2 ∂potentialMeasure φ) +
        weightedSuccessorHessianDefect (hφ.of_le (by simp)) hκ hlower U W +
          κ * ‖weightedFamilyGradient φ ι U‖ ^ 2 ≤
            ∑ i, ∫ x, weightedDiffusion φ (f i) x ^ 2 ∂potentialMeasure φ := by
  let hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  obtain ⟨W, hW, hWD, hHnorm, _, hB⟩ := exists_weightedFamily_hessian_of_diffusion_domain
    hφ2 hκ hlower U f (fun i => (hf i).of_le (by simp)) hv hL
  obtain ⟨fnext, hn⟩ := weightedNormalizedSuccessor_exists_smooth_representative hφ hκ hlower U f hf hv
  have hforce : (∑ ki, ∫ x, weightedDiffusion φ (fnext ki) x ^ 2 ∂potentialMeasure φ) =
      ‖weightedSuccessorForcing hφ2 hκ hlower U‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro ki _
    rw [realLp_norm_sq_eq_integral_sq_of_ae
      (weightedSuccessorForcing_ae_of_representative hφ2 hκ hlower U f
        (fun i => (hf i).of_le (by simp)) hv ki)]
    simp_rw [(hn ki).2.2.2.2.1, neg_sq]
  have hid := weightedSuccessor_hessian_energy_eq_forcing_add_defect hφ2 hκ hlower U W hW
  refine ⟨fnext, W, hn, hW, hWD,
    weightedSuccessor_hessian_orthogonal hφ2 hκ hlower U W hW, ?_, ?_⟩
  · rw [← hHnorm, hforce]
    exact hid
  · rw [hforce, ← hid]
    exact hB

end KLS
end

#print axioms KLS.weightedSuccessorForcing_ae_of_representative
#print axioms KLS.exists_weightedNormalizedSuccessor_bochner_step
