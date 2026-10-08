import KLS.TensorRankOne

/-! The second cumulant slice and its actual diffusion coefficient are the
covariance matrix and covariance-noise matrix applied to the fixed direction. -/
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem coordinateCumulantTensor_one (hμ : IsCompact μ.support)
    (u : Space n) (z : Fin (n+n*n) → ℝ) :
    coordinateCumulantTensor μ 1 u z = rankOneTensor (coordinateCovarianceMatrix μ z *ᵥ u.ofLp) := by
  let p := decodeState z
  let := law_isProbability hμ p.1 p.2
  have hν : IsCompact (law μ p.1 p.2).support := by rwa [support_law hμ]
  funext a
  change cumulantTensor (law μ p.1 p.2) 2 (cumulantSliceDirections u a) = _
  rw [cumulantTensor_two_apply hν]
  change ProbabilityTheory.covariance (fun x => inner ℝ u x)
    (fun x => inner ℝ (EuclideanSpace.single (a 0) 1) x) (law μ p.1 p.2) = _
  have he : (fun x : Space n => inner ℝ u x) = fun x => ∑ i : Fin n, u i * x i := by
    funext x
    rw [inner_eq_coordinate_sum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hb : (fun x : Space n => inner ℝ (EuclideanSpace.single (a 0) 1) x) = fun x => x (a 0) := by
    funext x
    simp [inner_eq_coordinate_sum]
  rw [he, hb]
  have hm (i : Fin n) : MemLp (fun x : Space n => x i) 2 (law μ p.1 p.2) :=
    memLp_two_continuous_tilted hμ (continuous_exponent p.1 p.2) (by fun_prop)
  rw [ProbabilityTheory.covariance_fun_sum_left (fun i => (hm i).const_mul _) (hm (a 0))]
  simp only [ProbabilityTheory.covariance_const_mul_left]
  change (∑ i, u i * ProbabilityTheory.covariance (fun x => x i) (fun x => x (a 0))
    (law μ p.1 p.2)) = ∑ i, covariance μ p.1 p.2 (a 0) i * u i
  apply Finset.sum_congr rfl
  intro i _
  rw [ProbabilityTheory.covariance_comm]
  exact mul_comm _ _

theorem nextCumulantTensor_one (hμ : IsCompact μ.support)
    (u : Space n) (z : Fin (n+n*n) → ℝ) (k : Fin n) :
    nextCumulantTensor μ 1 u k z = rankOneTensor (covarianceNoiseMatrix μ k z *ᵥ u.ofLp) := by
  rw [← fderiv_coordinateCumulantTensor_diffusion hμ]
  have he : coordinateCumulantTensor μ 1 u =
      fun y => covarianceSliceCLM u.ofLp (coordinateCovarianceMatrix μ y) :=
    funext (coordinateCumulantTensor_one hμ u)
  rw [he, fderiv_compCLM_apply (covarianceSliceCLM u.ofLp)
    ((contDiff_coordinateCovarianceMatrix hμ).differentiable (by simp) z),
    fderiv_coordinateCovarianceMatrix_diffusion hμ]
  rfl

theorem whitenedCumulantTensor_one (hμ : IsCompact μ.support)
    (u : Space n) (z : Fin (n+n*n) → ℝ) :
    whitenedCumulantTensor μ 1 u z = rankOneTensor
      (inverseSqrtCovariance μ (decodeState z) *ᵥ (coordinateCovarianceMatrix μ z *ᵥ u.ofLp)) := by
  rw [whitenedCumulantTensor, coordinateCumulantTensor_one hμ, tensorMatrix_rankOne]

theorem whitenedNextCumulantTensor_one (hμ : IsCompact μ.support)
    (u : Space n) (z : Fin (n+n*n) → ℝ) (k : Fin n) :
    whitenedNextCumulantTensor μ 1 u k z = rankOneTensor
      (inverseSqrtCovariance μ (decodeState z) *ᵥ (covarianceNoiseMatrix μ k z *ᵥ u.ofLp)) := by
  rw [whitenedNextCumulantTensor, nextCumulantTensor_one hμ, tensorMatrix_rankOne]

end KLS.AdaptiveLocalization
end
