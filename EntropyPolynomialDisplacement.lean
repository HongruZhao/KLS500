import EntropyFiniteDualDisplacement
import EntropyProfileFiniteGradient

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- Every term of the entropy-clock displacement sum is obtained from a
literal gradient bound on a constructed actual resolvent representative. -/
theorem weightedMassResolvent_finite_dual_polynomial_profile
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {t B M L : ℝ} (ht : 0 < t) (hB : 0 < B) (hM : 0 ≤ M)
    (hsmall : t*L ≤ B/2000) {g : Space n → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg2 : MemLp g 2 (potentialMeasure φ))
    (hgB : ∀ x, |g x| ≤ B) (hgM : ∀ x, ‖gradient g x‖ ≤ M)
    (hgL : ∀ x, |weightedDiffusion φ g x| ≤ L)
    {ψ : Space n → ℝ} (hψ : LocallyLipschitzTests (potentialMeasure φ) ψ)
    (heψ : energy (potentialMeasure φ) ψ < ⊤) {N : ℕ} (hN : 51 ≤ N) :
    |inner ℝ (hg2.toLp g-(weightedMassResolvent φ ht)^[N] (hg2.toLp g)) (hψ.2.toLp ψ)| ≤
      (51*t*M+∑ j ∈ Finset.range (N-51),
        t*(((87/100 : ℝ)*B)/(Real.sqrt (t/(101/100 : ℝ))*entropyClock (51+j))))*
          (∫ x, ‖gradient ψ x‖ ∂potentialMeasure φ) := by
  apply weightedMassResolvent_finite_dual_prefix_tail (hφ.of_le (by simp)) ht
    (hg2.toLp g) entropyClock hψ heψ hN
  intro k _hkN
  obtain ⟨v,hv,hvμ,hvM,hvG⟩ := weightedMassResolvent_exists_polynomial_entropy_gradient
    hφ hconv ht hB hM hsmall hg hg2 hgB hgM hgL k
  exact ⟨v,hv.of_le (by simp),hvμ,hvM,fun hk => hvG (by omega)⟩

end KLS.ConstantReduction
end
