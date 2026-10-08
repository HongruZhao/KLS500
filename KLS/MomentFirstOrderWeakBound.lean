import KLS.CompactLaplacianPairing

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Original weak moment transport, quadratic flatness, and density closeness
force the actual normalized distribution Laplacian test to be O(epsilon).
The local energy, C1 regularity, strict convexity, integrability, and localized
transport identity are all concluded from the earlier proved ingredients. -/
theorem moment_normalized_laplacian_pairing_bound (hn : 0 < n)
    {u V ψ χ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V) [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    {c ε R r S T M M₀ M₂ : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hR : 0 < R)
    (hRr : R ≤ r) (hrS : r < S) (hST : S < T)
    (hsmall : ε * M ≤ R ^ 2 / 16) (hM : 0 ≤ M) (hM₀ : 0 ≤ M₀) (hM₂ : 0 ≤ M₂)
    (hψs : tsupport ψ ⊆ closedBall (0 : Space n) (R / 4))
    (hχs : tsupport χ ⊆ closedBall (0 : Space n) r)
    (hχone : ∀ x ∈ closedBall (0 : Space n) R, χ x = 1)
    (hdensity : ∀ x ∈ closedBall (0 : Space n) T,
      |Real.exp (-u x + V (gradient u x)) - 1| ≤ ε ^ 2)
    (hbound : ∀ x ∈ closedBall (0 : Space n) T,
      |normalizedQuadraticError u 0 0 c ε x| ≤ M)
    (hψbound : ∀ x, |ψ x| ≤ M₀)
    (hHbound : ∀ x, ∀ i j, |coordinateHessian ψ x i j| ≤ M₂) :
    |∫ x, normalizedQuadraticError u 0 0 c ε x * coordinateLaplacian ψ x| ≤
      ε * ((n : ℝ) ^ 2 * M₂ *
        (32 * (M + r ^ 2) ^ 2 * (∫ x, ∑ i, coordinateDerivative χ i x ^ 2) +
          2 * n * r ^ 2 * (∫ x, χ x ^ 2)) + M₀ * (∫ x, χ x ^ 2)) := by
  have hu := moment_contDiff_one_closedTarget hLip hc hV hK hKc hpush
  have hstrict := moment_strictConvexOn hLip hc hV hK.measurableSet hKc hpush
  have hRT : R ≤ T := by linarith
  have hrT : r ≤ T := by linarith
  have hclose : ∀ x ∈ closedBall (0 : Space n) R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 c x| ≤ ε * M := by
    intro x hx
    exact abs_sub_quadratic_le_of_normalized_bound hε
      (hbound x (closedBall_subset_closedBall hRT hx))
  obtain ⟨hint, htransport⟩ := localized_moment_transport_of_quadratic_closeness
    hLip hc hV hK hKc hpush hψ.continuous hR hsmall hclose hψs
  have hh := abs_integral_gradient_pairing_le_of_localized_transport hu hstrict hψ hψc
    hχ.continuous hχc hR hsmall hε hM₀ hM₂ hclose hψs hχone
    (fun x hx => hdensity x (closedBall_subset_closedBall hRT hx)) hψbound hHbound hint htransport
  rw [integral_inner_gradient_eq_neg_laplacian_pairing
    (contDiff_normalizedQuadraticError hu _ _ _ _) hψ hψc, abs_neg,
    integral_cutoff_norm_gradient_sq_eq_coordinate_energy] at hh
  have he := moment_normalizedQuadraticError_caccioppoli hn hLip hc hV hK hKc hpush hχ hχc
    0 0 c hε hεhalf (by linarith : 0 < S) hrS hST hχs hdensity hM
    (fun x hx => hbound x (closedBall_subset_closedBall hrT (hχs hx)))
  have hcoeff : 0 ≤ (n : ℝ) ^ 2 * M₂ := mul_nonneg (sq_nonneg _) hM₂
  have hb := mul_le_mul_of_nonneg_left he hcoeff
  have ha := add_le_add hb (le_refl (M₀ * (∫ x, χ x ^ 2)))
  exact hh.trans (mul_le_mul_of_nonneg_left ha hε.le)

end KLS
end
