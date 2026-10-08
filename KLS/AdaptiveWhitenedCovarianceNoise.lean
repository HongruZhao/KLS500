import KLS.AdaptiveMaximalLogDetIto

/-! The whitened covariance noise is the actual third tensor of the normalized law. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.AdaptiveLocalization
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem integrable_continuous_law (hμ : IsCompact μ.support) (p : Parameter n)
    {f : Space n → ℝ} (hf : Continuous f) : Integrable f (law μ p.1 p.2) :=
  integrable_tilted_of_compact_support hμ (continuous_exponent p.1 p.2)
    (integrable_of_continuous_compact_support_measure hμ hf)

theorem normalizedCenteredVector_law_apply (hμ : IsCompact μ.support)
    (p : Parameter n) (x : Space n) (i : Fin n) :
    normalizedCenteredVector (law μ p.1 p.2) x i =
      ∑ j : Fin n, inverseSqrtCovariance μ p i j * (x j - mean μ p.1 p.2 j) := by
  letI := law_isProbability hμ p.1 p.2
  have hi : Integrable (fun x : Space n => x) (law μ p.1 p.2) := by
    have hid : MemLp (id : Space n → Space n) 2 (law μ p.1 p.2) := by
      apply MemLp.of_eval_piLp
      intro j
      exact memLp_two_continuous_tilted hμ (continuous_exponent p.1 p.2) (by fun_prop)
    exact hid.integrable (by norm_num)
  unfold normalizedCenteredVector
  rw [← covariance_eq_covarianceMatrix hμ p, matrixAction_apply]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [PiLp.sub_apply]
  congr 1
  exact ((EuclideanSpace.proj j).integral_comp_comm hi).symm

theorem projection_sub_average_eq_normalized (hμ : IsCompact μ.support)
    (p : Parameter n) (x : Space n) (k : Fin n) :
    projection μ p k x - tiltAverage μ (exponent p.1 p.2) (projection μ p k) =
      normalizedCenteredVector (law μ p.1 p.2) x k := by
  rw [average_projection hμ, normalizedCenteredVector_law_apply hμ]
  change (∑ i, inverseSqrtCovariance μ p i k * x i) -
      (∑ i, inverseSqrtCovariance μ p i k * mean μ p.1 p.2 i) = _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hs : inverseSqrtCovariance μ p i k = inverseSqrtCovariance μ p k i :=
    congrFun (congrFun (inverseSqrtCovariance_isSymm (μ := μ) p).eq k) i
  rw [hs]
  ring

theorem covarianceNoiseMatrix_eq_integral (hμ : IsCompact μ.support)
    (z : Fin (n+n*n) → ℝ) (i j k : Fin n) :
    covarianceNoiseMatrix μ k z i j =
      ∫ x, (x i - mean μ (decodeState z).1 (decodeState z).2 i) *
        (x j - mean μ (decodeState z).1 (decodeState z).2 j) *
        normalizedCenteredVector (law μ (decodeState z).1 (decodeState z).2) x k
        ∂law μ (decodeState z).1 (decodeState z).2 := by
  unfold covarianceNoiseMatrix
  rw [covarianceNoiseCoefficient_eq_thirdCumulant hμ]
  unfold tiltThirdCumulant
  change (∫ x, (x i - mean μ (decodeState z).1 (decodeState z).2 i) *
    (x j - mean μ (decodeState z).1 (decodeState z).2 j) *
    (projection μ (decodeState z) k x - tiltAverage μ (exponent (decodeState z).1 (decodeState z).2)
      (projection μ (decodeState z) k)) ∂law μ (decodeState z).1 (decodeState z).2) = _
  simp_rw [projection_sub_average_eq_normalized hμ]

def whitenedCovarianceNoiseMatrix (μ : Measure (Space n)) (k : Fin n)
    (z : Fin (n+n*n) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  inverseSqrtCovariance μ (decodeState z) * covarianceNoiseMatrix μ k z *
    inverseSqrtCovariance μ (decodeState z)

/-- Congruence by the actual principal inverse square root converts covariance
noise into the actual covariance-normalized third centered tensor. -/
theorem whitenedCovarianceNoiseMatrix_eq_integral (hμ : IsCompact μ.support)
    (z : Fin (n+n*n) → ℝ) (i j k : Fin n) :
    whitenedCovarianceNoiseMatrix μ k z i j =
      ∫ x, normalizedCenteredVector (law μ (decodeState z).1 (decodeState z).2) x i *
        normalizedCenteredVector (law μ (decodeState z).1 (decodeState z).2) x j *
        normalizedCenteredVector (law μ (decodeState z).1 (decodeState z).2) x k
        ∂law μ (decodeState z).1 (decodeState z).2 := by
  let p := decodeState z
  let S := inverseSqrtCovariance μ p
  let c : Space n → Fin n → ℝ := fun x a => x a - mean μ p.1 p.2 a
  let y := normalizedCenteredVector (law μ p.1 p.2)
  have hy : Continuous y := continuous_normalizedCenteredVector _
  have hs (a b : Fin n) : S a b = S b a :=
    congrFun (congrFun (inverseSqrtCovariance_isSymm (μ := μ) p).eq b) a
  have hInt (a b : Fin n) : Integrable (fun x => S i a * S j b * (c x a * c x b * y x k))
      (law μ p.1 p.2) := integrable_continuous_law hμ p (by dsimp [c]; fun_prop)
  calc
    _ = ∑ a : Fin n, ∑ b : Fin n,
        S i a * S j b * (∫ x, c x a * c x b * y x k ∂law μ p.1 p.2) := by
      unfold whitenedCovarianceNoiseMatrix
      rw [Matrix.mul_assoc]
      simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [covarianceNoiseMatrix_eq_integral hμ]
      change S i a * (_ * S b j) = S i a * S j b * _
      rw [hs b j]
      ring
    _ = ∫ x, ∑ a : Fin n, ∑ b : Fin n,
        S i a * S j b * (c x a * c x b * y x k) ∂law μ p.1 p.2 := by
      rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => hInt a b)]
      apply Finset.sum_congr rfl
      intro a _
      rw [integral_finsetSum _ (fun b _ => hInt a b)]
      simp only [integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      change (∑ a : Fin n, ∑ b : Fin n, S i a * S j b * (c x a * c x b * y x k)) =
        y x i * y x j * y x k
      have hyi := normalizedCenteredVector_law_apply hμ p x i
      have hyj := normalizedCenteredVector_law_apply hμ p x j
      change y x i = ∑ a, S i a * c x a at hyi
      change y x j = ∑ b, S j b * c x b at hyj
      rw [hyi, hyj]
      simp only [Finset.sum_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.whitenedCovarianceNoiseMatrix_eq_integral
