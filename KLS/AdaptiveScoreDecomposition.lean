import KLS.AdaptiveDiffusionCovariance

/-! Decomposition of the actual adaptive drift score into its Brownian
projection scores, using the principal inverse-square-root covariance identity. -/
open MeasureTheory ProbabilityTheory Set Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS.AdaptiveLocalization
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def projection (μ : Measure (Space n)) (p : Parameter n) (k : Fin n) (x : Space n) : ℝ :=
  ∑ i, inverseSqrtCovariance μ p i k * x i

theorem continuous_projection (p : Parameter n) (k : Fin n) : Continuous (projection μ p k) := by
  unfold projection
  fun_prop

theorem projection_eq_transpose_mulVec (p : Parameter n) (k : Fin n) (x : Space n) :
    projection μ p k x = ((inverseSqrtCovariance μ p).transpose *ᵥ (fun i => x i)) k := rfl

theorem exponent_diffusion_eq_projection (p : Parameter n) (k : Fin n) :
    exponent (diffusion μ k p).1 (diffusion μ k p).2 = projection μ p k := by
  funext x
  simp [diffusion, exponent, projection]

theorem average_projection (hμ : IsCompact μ.support) (p : Parameter n) (k : Fin n) :
    tiltAverage μ (exponent p.1 p.2) (projection μ p k) =
      ((inverseSqrtCovariance μ p).transpose *ᵥ mean μ p.1 p.2) k := by
  letI := law_isProbability hμ p.1 p.2
  have hi (i : Fin n) : Integrable (fun x : Space n => inverseSqrtCovariance μ p i k * x i)
      (law μ p.1 p.2) := by
    exact integrable_tilted_of_compact_support hμ (continuous_exponent p.1 p.2)
      (integrable_of_continuous_compact_support_measure hμ (by fun_prop))
  change (∫ x, (∑ i, inverseSqrtCovariance μ p i k * x i) ∂law μ p.1 p.2) =
    ∑ i, inverseSqrtCovariance μ p i k * (∫ x, x i ∂law μ p.1 p.2)
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [integral_const_mul]

theorem covariance_projection (hμ : IsCompact μ.support) (p : Parameter n) (i k : Fin n) :
    ProbabilityTheory.covariance (fun x : Space n => x i) (projection μ p k) (law μ p.1 p.2) =
      (covariance μ p.1 p.2 * inverseSqrtCovariance μ p) i k := by
  letI := law_isProbability hμ p.1 p.2
  have hm (a : Space n → ℝ) (ha : Continuous a) : MemLp a 2 (law μ p.1 p.2) :=
    memLp_two_continuous_tilted hμ (continuous_exponent p.1 p.2) ha
  unfold projection
  rw [ProbabilityTheory.covariance_fun_sum_right (fun j => hm _ (by fun_prop))
    (hm _ (by fun_prop))]
  simp only [ProbabilityTheory.covariance_const_mul_right, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem dotProduct_gram_mulVec (S : Matrix (Fin n) (Fin n) ℝ) (v w : Fin n → ℝ) :
    v ⬝ᵥ (S * S.transpose) *ᵥ w = (S.transpose *ᵥ v) ⬝ᵥ (S.transpose *ᵥ w) := by
  rw [← Matrix.mulVec_mulVec]
  rw [← Matrix.dotProduct_transpose_mulVec S (S.transpose *ᵥ w) v]
  exact dotProduct_comm _ _

/-- The actual drift score is the finite sum E[h_k] h_k - h_k^2/2. -/
theorem exponent_drift_eq_projection_sum (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (p : Parameter n) :
    exponent (drift μ p).1 (drift μ p).2 = fun x =>
      ∑ k, (tiltAverage μ (exponent p.1 p.2) (projection μ p k) * projection μ p k x +
        (-(projection μ p k x)^2 / 2)) := by
  funext x
  rw [exponent_eq_dotProduct]
  change (inverseCovariance μ p *ᵥ mean μ p.1 p.2) ⬝ᵥ (fun i => x i) -
      (fun i => x i) ⬝ᵥ inverseCovariance μ p *ᵥ (fun i => x i) / 2 = _
  rw [← inverseSqrtCovariance_mul_transpose hμ hfull p]
  rw [dotProduct_comm ((inverseSqrtCovariance μ p * (inverseSqrtCovariance μ p).transpose) *ᵥ
    mean μ p.1 p.2) (fun i => x i)]
  rw [dotProduct_gram_mulVec, dotProduct_gram_mulVec]
  simp only [average_projection hμ, projection_eq_transpose_mulVec, dotProduct, Finset.sum_div]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.exponent_drift_eq_projection_sum
#print axioms KLS.AdaptiveLocalization.covariance_projection
