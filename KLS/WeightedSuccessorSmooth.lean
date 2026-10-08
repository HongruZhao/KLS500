import KLS.WeightedSuccessorOrthogonality
import KLS.WeightedPoissonRegularity

/-! The actual normalized successor of a smooth energy-graph representative
has a smooth classical representative in the L² diffusion domain. The genuine
Poisson regularity theorem constructs that representative componentwise. -/

open MeasureTheory InnerProductSpace Matrix Filter
open scoped ContDiff RealInnerProductSpace ENNReal

noncomputable section
namespace KLS
variable {n : ℕ}

/-- Smooth representatives are preserved by the actual normalized successor.
No regularity, growth, or diffusion-domain assumption on the successor is an input. -/
theorem weightedNormalizedSuccessor_exists_smooth_representative
    {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι) (f : ι → Space n → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hv : ∀ i, f i =ᵐ[volume] (weightedH1Value φ (U i) : Space n → ℝ)) :
    ∃ fnext : (Fin n × ι) → Space n → ℝ, ∀ ki,
      ContDiff ℝ (⊤ : ℕ∞) (fnext ki) ∧ MemLp (fnext ki) 2 (potentialMeasure φ) ∧
      (∫ x, fnext ki x ∂potentialMeasure φ) = 0 ∧
      fnext ki =ᵐ[volume] (weightedH1Value φ
        (weightedNormalizedSuccessor (hφ.of_le (by simp)) hκ hlower U ki) : Space n → ℝ) ∧
      (∀ x, weightedDiffusion φ (fnext ki) x =
        -(weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower U *
          (coordinateDerivative (f ki.2) ki.1 x -
            ∫ y, coordinateDerivative (f ki.2) ki.1 y ∂potentialMeasure φ))) ∧
      MemLp (weightedDiffusion φ (fnext ki)) 2 (potentialMeasure φ) := by
  let hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  let a := weightedSuccessorScale hφ2 hκ hlower U
  have hd (i : ι) (k : Fin n) : coordinateDerivative (f i) k
      =ᵐ[potentialMeasure φ] (weightedH1Derivative φ k (U i) : Space n → ℝ) :=
    (withDensity_absolutelyContinuous _ _).ae_eq
      (weightedH1_coordinateDerivative_of_representative (hφ.of_le (by simp)) (U i)
        ((hf i).of_le (by simp)) (hv i) k)
  have hdf (i : ι) (k : Fin n) : MemLp (coordinateDerivative (f i) k) 2 (potentialMeasure φ) :=
    (memLp_congr_ae (hd i k)).mpr (Lp.memLp _)
  have hnext (ki : Fin n × ι) : ∃ v : Space n → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) v ∧ MemLp v 2 (potentialMeasure φ) ∧
      (∫ x, v x ∂potentialMeasure φ) = 0 ∧
      v =ᵐ[volume] (weightedH1Value φ
        (weightedNormalizedSuccessor hφ2 hκ hlower U ki) : Space n → ℝ) ∧
      (∀ x, weightedDiffusion φ v x =
        -(a * (coordinateDerivative (f ki.2) ki.1 x -
          ∫ y, coordinateDerivative (f ki.2) ki.1 y ∂potentialMeasure φ))) ∧
      MemLp (weightedDiffusion φ v) 2 (potentialMeasure φ) := by
    let g : Space n → ℝ := fun x => a * (coordinateDerivative (f ki.2) ki.1 x -
      ∫ y, coordinateDerivative (f ki.2) ki.1 y ∂potentialMeasure φ)
    have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
      contDiff_const.mul ((contDiff_coordinateDerivative (hf ki.2) (m := (⊤ : ℕ∞))
        (by simp) ki.1).sub contDiff_const)
    have hg2 : MemLp g 2 (potentialMeasure φ) :=
      ((hdf ki.2 ki.1).sub (memLp_const _)).const_mul a
    have hgm : (∫ x, g x ∂potentialMeasure φ) = 0 := by
      dsimp only [g]
      rw [integral_const_mul, integral_sub ((hdf ki.2 ki.1).integrable (by norm_num))
        (integrable_const _)]
      simp
    have hgi : hg2.toLp g =
        a • weightedFamilyCenteredGradient φ ι U ki := by
      apply Lp.ext
      have hi : (∫ x, coordinateDerivative (f ki.2) ki.1 x ∂potentialMeasure φ) =
          ∫ x, weightedH1Derivative φ ki.1 (U ki.2) x ∂potentialMeasure φ :=
        integral_congr_ae (hd ki.2 ki.1)
      have hcenter : (weightedFamilyCenteredGradient φ ι U ki : Space n → ℝ)
          =ᵐ[potentialMeasure φ] fun x => weightedH1Derivative φ ki.1 (U ki.2) x -
            ∫ y, weightedH1Derivative φ ki.1 (U ki.2) y ∂potentialMeasure φ := by
        rcases ki with ⟨k, i⟩
        rw [weightedFamilyCenteredGradient_apply]
        exact CenteredL2.center_ae (potentialMeasure φ) _
      filter_upwards [hg2.coeFn_toLp, Lp.coeFn_smul a (weightedFamilyCenteredGradient φ ι U ki),
        hcenter, hd ki.2 ki.1] with x hx hs hc hd'
      rw [hx, hs, Pi.smul_apply, smul_eq_mul, hc]
      dsimp only [g]
      rw [hi, hd']
    have hInv : weightedEnergyInverse hφ2 hκ hlower (hg2.toLp g) =
        weightedNormalizedSuccessor hφ2 hκ hlower U ki := by
      rw [hgi, map_smul]
      rfl
    obtain ⟨v, hvsm, hv2, hvm, _, hvrep, hveq⟩ :=
      weightedEnergyInverse_exists_smooth_representative hφ hκ hlower hg hg2
    have hvrep' : v =ᵐ[volume] (weightedH1Value φ
        (weightedNormalizedSuccessor hφ2 hκ hlower U ki) : Space n → ℝ) := by
      simpa only [hInv] using hvrep
    have hLeq : weightedDiffusion φ v = fun x => -g x := by
      funext x
      simpa only [hgm, sub_zero] using hveq x
    refine ⟨v, hvsm, hv2, hvm, hvrep', ?_, ?_⟩
    · intro x
      exact congrFun hLeq x
    · rw [hLeq]
      exact hg2.neg
  choose fnext hnext using hnext
  exact ⟨fnext, hnext⟩

end KLS
end

#print axioms KLS.weightedNormalizedSuccessor_exists_smooth_representative
