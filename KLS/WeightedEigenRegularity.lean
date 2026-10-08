import KLS.WeightedEigenClassical
import KLS.WeightedOptimalPoincare
import EllipticPdes.Regularity.Local.Evans

/-! Classical smooth representatives are derived from the actual graph weak eigenpair. -/

open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
open EllipticPdes.Sobolev EllipticPdes.Embedding EllipticPdes.Regularity
variable {n : ℕ}

/-- The actual weighted graph coordinates are the ordinary local weak gradient on the whole space. -/
theorem weightedH1_hasWeakGradOn_univ {φ : Space n → ℝ} (hφ : ContDiff ℝ 1 φ)
    (U : WeightedCenteredH1 φ) :
    HasWeakGradOn univ (weightedH1Value φ U) (fun i => weightedH1Derivative φ i U) := by
  intro ψ hψ hc _ i
  simpa only [Measure.restrict_univ, partialD, coordinateDerivative] using
    weightedH1_unweighted_weak_identity hφ U (hψ.of_le (by simp)) hc i

/-- The derived ordinary drift equation is precisely the upstream local elliptic weak formulation.
Its datum is zero; the eigenvalue is placed in the zeroth-order coefficient. -/
theorem weighted_eigenpair_localWeakSol {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 3 φ)
    {lam : ℝ} {U : WeightedCenteredH1 φ}
    (hw : ∀ V : WeightedCenteredH1 φ, weightedEnergyForm φ U V =
      lam * inner ℝ (weightedH1Value φ U) (weightedH1Value φ V)) :
    LocalWeakSol univ (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ))
      (fun x i => coordinateDerivative φ i x) (fun _ => -lam) (fun _ => 0)
      (weightedH1Value φ U) (fun i => weightedH1Derivative φ i U) := by
  intro ψ hψ hc _
  have h := weighted_eigenpair_unweighted_test hφ hw (hψ.of_le (by simp)) hc
  simp only [Measure.restrict_univ]
  have hdiag (i j : Fin n) :
      (∫ x, (1 : Matrix (Fin n) (Fin n) ℝ) i j * weightedH1Derivative φ i U x * partialD j ψ x) =
      if i = j then (∫ x, weightedH1Derivative φ i U x * partialD i ψ x) else 0 := by
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  have hz : (∫ x, -lam * weightedH1Value φ U x * ψ x) =
      -lam * ∫ x, weightedH1Value φ U x * ψ x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun _ => by ring
  simp_rw [hdiag]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, hz, zero_mul, integral_zero]
  change (∑ i : Fin n, ∫ x, weightedH1Derivative φ i U x * coordinateDerivative ψ i x) +
      (∑ i : Fin n, ∫ x, coordinateDerivative φ i x * weightedH1Derivative φ i U x * ψ x) +
      (-lam) * (∫ x, weightedH1Value φ U x * ψ x) = 0
  linarith

/-- The smooth local elliptic operator has actual identity principal part, actual potential
 gradient as drift, and the negative eigenvalue as zeroth-order coefficient. -/
def weightedEigenSmoothOp {φ : Space n → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (lam : ℝ) :
    SmoothOpOn n (univ : Set (Space n)) where
  a _ := (1 : Matrix (Fin n) (Fin n) ℝ)
  lam := 1
  lam_pos := zero_lt_one
  contDiffOn _ _ := contDiffOn_const
  elliptic := Eventually.of_forall fun x ξ => by
    simp [Matrix.one_apply, ite_mul, pow_two]
  b x i := coordinateDerivative φ i x
  c _ := -lam
  b_smooth i := (contDiff_coordinateDerivative hφ (m := (⊤ : ℕ∞)) (by simp) i).contDiffOn
  c_smooth := contDiffOn_const

/-- A genuine weak weighted eigenpair has an actual globally smooth representative when the
potential is smooth. Local L² and the weak equation are proved from its actual graph coordinates;
no regularity, boundedness, support, or growth hypothesis is imposed on the eigenfunction. -/
theorem weighted_eigenpair_exists_smooth_representative {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {lam : ℝ} {U : WeightedCenteredH1 φ}
    (hw : ∀ V : WeightedCenteredH1 φ, weightedEnergyForm φ U V =
      lam * inner ℝ (weightedH1Value φ U) (weightedH1Value φ V)) :
    ∃ f : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      f =ᵐ[volume] (weightedH1Value φ U : Space n → ℝ) ∧
      f =ᵐ[potentialMeasure φ] (weightedH1Value φ U : Space n → ℝ) := by
  obtain ⟨f, hs, hae⟩ := exists_contDiffOn_of_localWeakSol isOpen_univ
    (weightedEigenSmoothOp hφ lam) (f := fun _ => 0) contDiffOn_const
    (fun K hK _ => weightedH1Value_memLp_restrict hφ.continuous U hK)
    (fun i K hK _ => weightedH1Derivative_memLp_restrict hφ.continuous U i hK)
    (weightedH1_hasWeakGradOn_univ (hφ.of_le (by simp)) U)
    (weighted_eigenpair_localWeakSol (hφ.of_le (by simp)) hw)
  have hv : f =ᵐ[volume] (weightedH1Value φ U : Space n → ℝ) := by
    simpa only [Measure.restrict_univ] using hae
  exact ⟨f, contDiffOn_univ.mp hs, hv, (withDensity_absolutelyContinuous _ _).ae_eq hv⟩

/-- The actual attained first eigenpair has a classical smooth, normalized representative
with its exact Dirichlet energy and the faithful optimal Poincaré reciprocal. All regularity of
the eigenfunction is concluded from the smooth potential and the genuine weak solution. -/
theorem exists_positive_classical_eigenpair_with_optimal_poincare {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hn : 0 < n) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) :
    ∃ (lam : ℝ) (f : Space n → ℝ), κ ≤ lam ∧ 0 < lam ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧ MemLp f 2 (potentialMeasure φ) ∧
      (∫ x, f x ∂potentialMeasure φ) = 0 ∧
      (∫ x, f x ^ 2 ∂potentialMeasure φ) = 1 ∧
      (∀ x, weightedDiffusion φ f x = -lam * f x) ∧
      energy (potentialMeasure φ) f = ENNReal.ofReal lam ∧
      poincareConstant (potentialMeasure φ) = ENNReal.ofReal lam⁻¹ := by
  obtain ⟨lam, U, hk, hp, hu, hw, _, hcp⟩ :=
    exists_positive_weighted_eigenpair_with_optimal_poincare hn (hφ.of_le (by simp)) hκ hlower
  obtain ⟨f, hf, hv, hvμ⟩ := weighted_eigenpair_exists_smooth_representative hφ hw
  have hf2 : MemLp f 2 (potentialMeasure φ) := (memLp_congr_ae hvμ).mpr (Lp.memLp _)
  have hmean : (∫ x, f x ∂potentialMeasure φ) = 0 := by
    rw [integral_congr_ae hvμ, weightedH1_integral_eq_zero hφ.continuous U]
  have hsq : (∫ x, f x ^ 2 ∂potentialMeasure φ) = 1 := by
    calc
      _ = ∫ x, weightedH1Value φ U x ^ 2 ∂potentialMeasure φ := by
        apply integral_congr_ae
        filter_upwards [hvμ] with x hx
        rw [hx]
      _ = ‖weightedH1Value φ U‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, L2.real_inner_eq_integral]
        simp only [pow_two]
      _ = 1 := by rw [hu, one_pow]
  have hdf (i : Fin n) : coordinateDerivative f i =ᵐ[potentialMeasure φ]
      (weightedH1Derivative φ i U : Space n → ℝ) :=
    (withDensity_absolutelyContinuous _ _).ae_eq
      (weightedH1_coordinateDerivative_of_representative (hφ.of_le (by simp)) U
        (hf.of_le (by simp)) hv i)
  have hd2 (i : Fin n) : MemLp (coordinateDerivative f i) 2 (potentialMeasure φ) :=
    (memLp_congr_ae (hdf i)).mpr (Lp.memLp _)
  have he := energy_lt_top_of_memLp_coordinateDerivative hd2
  have hv' : (weightedH1Value φ U : Space n → ℝ) =ᵐ[potentialMeasure φ]
      fun x => f x - ∫ y, f y ∂potentialMeasure φ := by
    simpa only [hmean, sub_zero] using hvμ.symm
  have hnorm := weightedH1_faithful_test_norms
    (show LocallyLipschitzTests (potentialMeasure φ) f from
      ⟨(hf.of_le (by simp : (1 : ℕ∞ω) ≤ (⊤ : ℕ∞))).locallyLipschitz, hf2⟩)
    he hv' (fun i => (hdf i).symm)
  have hself : weightedEnergyForm φ U U = lam := by
    simpa only [real_inner_self_eq_norm_sq, hu, one_pow, mul_one] using hw U
  refine ⟨lam, f, hk, hp, hf, hf2, hmean, hsq,
    weighted_eigenpair_pointwise_of_representative (hφ.of_le (by simp)) hw
      (hf.of_le (by simp)) hv, ?_, hcp⟩
  simpa only [hself] using hnorm.2.2.2

end KLS
end

#print axioms KLS.weighted_eigenpair_exists_smooth_representative

#print axioms KLS.exists_positive_classical_eigenpair_with_optimal_poincare
