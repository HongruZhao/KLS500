import KLS.WeightedSuccessorOrthogonality
import KLS.WeightedBochnerDomain
import KLS.WeightedFaithfulGraph
import KLS.WeightedEigenClassical

/-! The genuine smooth diffusion domain supplies the actual graph Hessian
needed in the normalized successor identities. Hessian integrability and
admissibility of the centered derivatives are conclusions, not assumptions. -/

open MeasureTheory InnerProductSpace Matrix Filter
open scoped ContDiff RealInnerProductSpace ENNReal

noncomputable section
namespace KLS
variable {n : ℕ}

lemma realLp_norm_sq_eq_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (u : Lp ℝ 2 μ) : ‖u‖ ^ 2 = ∫ x, u x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial, pow_two]

lemma realLp_norm_sq_eq_integral_sq_of_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {u : Lp ℝ 2 μ} {f : Ω → ℝ} (h : (u : Ω → ℝ) =ᵐ[μ] f) :
    ‖u‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [realLp_norm_sq_eq_integral_sq]
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

theorem weightedH1Gradient_norm_sq_of_derivative_representative
    {φ f : Space n → ℝ} (U : WeightedCenteredH1 φ)
    (hd : ∀ j : Fin n, (weightedH1Derivative φ j U : Space n → ℝ)
      =ᵐ[potentialMeasure φ] coordinateDerivative f j) :
    ‖weightedH1Gradient φ U‖ ^ 2 = ∫ x, ‖gradient f x‖ ^ 2 ∂potentialMeasure φ := by
  have hf2 (j : Fin n) : MemLp (coordinateDerivative f j) 2 (potentialMeasure φ) :=
    (memLp_congr_ae (hd j)).mp (Lp.memLp _)
  rw [weightedH1Gradient_norm_sq]
  simp_rw [realLp_norm_sq_eq_integral_sq_of_ae (hd _)]
  rw [← integral_finsetSum Finset.univ (fun j _ => (hf2 j).integrable_sq)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [EuclideanSpace.real_norm_sq_eq, coordinateDerivative_eq_gradient]

/-- A smooth representative in the actual diffusion domain produces genuine
H1 representatives of all centered derivatives, and the sharp summed Bochner bound. -/
theorem exists_weightedFamily_hessian_of_diffusion_domain
    {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι) (f : ι → Space n → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i))
    (hv : ∀ i, f i =ᵐ[volume] (weightedH1Value φ (U i) : Space n → ℝ))
    (hL : ∀ i, MemLp (weightedDiffusion φ (f i)) 2 (potentialMeasure φ)) :
    ∃ W : WeightedH1Family φ (Fin n × ι),
      weightedFamilyValue φ (Fin n × ι) W = weightedFamilyCenteredGradient φ ι U ∧
      (∀ j k i, (weightedH1Derivative φ j (W (k, i)) : Space n → ℝ)
        =ᵐ[potentialMeasure φ] fun x => coordinateHessian (f i) x j k) ∧
      ‖weightedFamilyGradient φ (Fin n × ι) W‖ ^ 2 =
        ∑ i, ∫ x, hessianSquare (f i) x ∂potentialMeasure φ ∧
      ‖weightedFamilyGradient φ ι U‖ ^ 2 =
        ∑ i, ∫ x, ‖gradient (f i) x‖ ^ 2 ∂potentialMeasure φ ∧
      ‖weightedFamilyGradient φ (Fin n × ι) W‖ ^ 2 + κ * ‖weightedFamilyGradient φ ι U‖ ^ 2 ≤
        ∑ i, ∫ x, weightedDiffusion φ (f i) x ^ 2 ∂potentialMeasure φ := by
  have hd (i : ι) (j : Fin n) : coordinateDerivative (f i) j
      =ᵐ[potentialMeasure φ] (weightedH1Derivative φ j (U i) : Space n → ℝ) :=
    (withDensity_absolutelyContinuous _ _).ae_eq
      (weightedH1_coordinateDerivative_of_representative (hφ.of_le (by norm_num)) (U i)
        ((hf i).of_le (by norm_num)) (hv i) j)
  have hdf (i : ι) (j : Fin n) : MemLp (coordinateDerivative (f i) j) 2 (potentialMeasure φ) :=
    (memLp_congr_ae (hd i j)).mpr (Lp.memLp _)
  have hG (i : ι) : Integrable (fun x => ‖gradient (f i) x‖ ^ 2) (potentialMeasure φ) :=
    integrable_gradient_norm_sq_of_energy_lt_top
      (energy_lt_top_of_memLp_coordinateDerivative (hdf i))
  have hH (i : ι) : Integrable (hessianSquare (f i)) (potentialMeasure φ) :=
    (integrable_bochner_terms_of_diffusion_domain hφ (hf i)
      (fun x => (mul_nonneg hκ.le (sq_nonneg _)).trans
        (hessianGradientForm_lower_bound hlower x)) (hL i) (hG i)).1
  have hHij (i : ι) (j k : Fin n) :
      MemLp (fun x => coordinateHessian (f i) x j k) 2 (potentialMeasure φ) :=
    memLp_coordinateHessian_of_integrable_hessianSquare ((hf i).of_le (by norm_num)) (hH i) j k
  have hrep (ki : Fin n × ι) : ∃ V : WeightedCenteredH1 φ,
      (weightedH1Value φ V : Space n → ℝ) =ᵐ[potentialMeasure φ]
        (fun x => coordinateDerivative (f ki.2) ki.1 x -
          ∫ y, coordinateDerivative (f ki.2) ki.1 y ∂potentialMeasure φ) ∧
      ∀ j, (weightedH1Derivative φ j V : Space n → ℝ)
        =ᵐ[potentialMeasure φ] fun x => coordinateHessian (f ki.2) x j ki.1 := by
    have ht : LocallyLipschitzTests (potentialMeasure φ) (coordinateDerivative (f ki.2) ki.1) :=
      ⟨(contDiff_coordinateDerivative (hf ki.2) (m := 1) (by norm_num) ki.1).locallyLipschitz,
        hdf ki.2 ki.1⟩
    exact exists_weightedH1_of_faithful_test hφ.continuous ht
      (energy_lt_top_of_memLp_coordinateDerivative (fun j => hHij ki.2 j ki.1))
  choose V hV hD using hrep
  let W : WeightedH1Family φ (Fin n × ι) := WithLp.toLp 2 V
  have hW : weightedFamilyValue φ (Fin n × ι) W = weightedFamilyCenteredGradient φ ι U := by
    apply PiLp.ext
    rintro ⟨k, i⟩
    rw [weightedFamilyValue_apply, weightedFamilyCenteredGradient_apply]
    apply Lp.ext
    have hi : (∫ x, coordinateDerivative (f i) k x ∂potentialMeasure φ) =
        ∫ x, weightedH1Derivative φ k (U i) x ∂potentialMeasure φ := integral_congr_ae (hd i k)
    filter_upwards [hV (k, i), hd i k,
      CenteredL2.center_ae (potentialMeasure φ) (weightedH1Derivative φ k (U i))] with x hx hy hz
    change weightedH1Value φ (V (k, i)) x = _
    rw [hx, hi, hy, hz]
  have hWD (j k : Fin n) (i : ι) :
      (weightedH1Derivative φ j (W (k, i)) : Space n → ℝ)
        =ᵐ[potentialMeasure φ] fun x => coordinateHessian (f i) x j k := hD (k, i) j
  have hWnorm : ‖weightedFamilyGradient φ (Fin n × ι) W‖ ^ 2 =
      ∑ i, ∫ x, hessianSquare (f i) x ∂potentialMeasure φ := by
    rw [weightedFamilyGradient_norm_sq, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    have hnorm (j k : Fin n) : ‖weightedH1Derivative φ j (W (k, i))‖ ^ 2 =
        ∫ x, coordinateHessian (f i) x j k ^ 2 ∂potentialMeasure φ :=
      realLp_norm_sq_eq_integral_sq_of_ae (hWD j k i)
    simp_rw [hnorm]
    simp only [hessianSquare]
    rw [integral_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum _ (fun k _ => (hHij i j k).integrable_sq))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finsetSum Finset.univ (fun k _ => (hHij i j k).integrable_sq)]
  have hUnorm : ‖weightedFamilyGradient φ ι U‖ ^ 2 =
      ∑ i, ∫ x, ‖gradient (f i) x‖ ^ 2 ∂potentialMeasure φ := by
    rw [weightedFamilyGradient_norm_sq]
    apply Finset.sum_congr rfl
    intro i _
    rw [← weightedH1Gradient_norm_sq]
    exact weightedH1Gradient_norm_sq_of_derivative_representative (U i) (fun j => (hd i j).symm)
  refine ⟨W, hW, hWD, hWnorm, hUnorm, ?_⟩
  rw [hWnorm, hUnorm, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ =>
    integral_hessianSquare_add_curvature_gradient_le_diffusion_sq hφ (hf i) hκ.le hlower (hL i) (hG i))

end KLS
end

#print axioms KLS.exists_weightedFamily_hessian_of_diffusion_domain
