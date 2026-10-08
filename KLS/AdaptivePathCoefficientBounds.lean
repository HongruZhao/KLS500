import KLS.AdaptiveCovarianceCompactBounds

/-! Actual drift and diffusion coefficients remain bounded on finite horizons before lifetime. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.AdaptiveLocalization
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem norm_encodeState_le {p : Parameter n} {K : ℝ} (hK : 0 ≤ K)
    (hc : ‖p.1‖ ≤ K) (hQ : ‖p.2‖ ≤ K) : ‖encodeState p‖ ≤ K := by
  apply (pi_norm_le_iff_of_nonneg hK).mpr
  intro a
  refine Fin.addCases ?_ ?_ a
  · intro i
    simp only [encodeState, Fin.addCases_left]
    exact (norm_le_pi_norm p.1 i).trans hc
  · intro ij
    simp only [encodeState, Fin.addCases_right]
    exact ((norm_le_pi_norm (p.2 (finProdFinEquiv.symm ij).1) (finProdFinEquiv.symm ij).2).trans
      (norm_le_pi_norm p.2 (finProdFinEquiv.symm ij).1)).trans hQ

theorem norm_linearDrift_le_of_bounds (p : Parameter n) {C R : ℝ} (hC0 : 0 ≤ C) (hR0 : 0 ≤ R)
    (hC : ‖inverseCovariance μ p‖ ≤ C) (hR : ‖mean μ p.1 p.2‖ ≤ R) :
    ‖linearDrift μ p‖ ≤ (n : ℝ)*C*R := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖∑ j : Fin n, inverseCovariance μ p i j * mean μ p.1 p.2 j‖ ≤ _
  calc
    _ ≤ ∑ j : Fin n, ‖inverseCovariance μ p i j * mean μ p.1 p.2 j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, C*R := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      apply mul_le_mul
        (((norm_le_pi_norm (inverseCovariance μ p i) j).trans
          (norm_le_pi_norm (inverseCovariance μ p) i)).trans hC)
        ((norm_le_pi_norm (mean μ p.1 p.2) j).trans hR) (norm_nonneg _) hC0
    _ = _ := by simp; ring

theorem coordinateCoefficients_bound_of_inverse (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (z : Fin (n+n*n) → ℝ) {C R : ℝ}
    (hC0 : 0 ≤ C) (hR0 : 0 ≤ R)
    (hC : ‖inverseCovariance μ (decodeState z)‖ ≤ C)
    (hR : ‖mean μ (decodeState z).1 (decodeState z).2‖ ≤ R) :
    ‖coordinateDrift μ z‖ ≤ (n : ℝ)*C*R+C+1 ∧
      ∀ k : Fin n, ‖coordinateDiffusion μ k z‖ ≤ (n : ℝ)*C*R+C+1 := by
  have hprod : 0 ≤ (n : ℝ)*C*R := by positivity
  have hK : 0 ≤ (n : ℝ)*C*R+C+1 := by positivity
  constructor
  · apply norm_encodeState_le hK
    · exact (norm_linearDrift_le_of_bounds _ hC0 hR0 hC hR).trans (by linarith)
    · exact hC.trans (by linarith)
  · intro k
    apply norm_encodeState_le hK
    · have hs := norm_inverseSqrtCovariance_le_of_inverse hμ hfull (decodeState z) hC0 hC
      apply (pi_norm_le_iff_of_nonneg hK).mpr
      intro i
      exact (((norm_le_pi_norm (inverseSqrtCovariance μ (decodeState z) i) k).trans
        (norm_le_pi_norm (inverseSqrtCovariance μ (decodeState z)) i)).trans hs).trans (by linarith)
    · simpa only [diffusion, norm_zero] using hK

open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW)

/-- On one common event, every finite horizon has a finite bound on all original
coefficients evaluated along the actual maximal path before its lifetime. -/
theorem ae_finite_horizon_coefficient_bound (hμ : IsCompact μ.support)
    (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A) :
    ∀ᵐ ω ∂P, ∀ T : ℝ, 0 ≤ T → ∃ K : ℝ, 0 ≤ K ∧
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) T → (t : WithTop ℝ) < D.lifetime ω →
        ‖coordinateDrift μ (D.path t ω)‖ ≤ K ∧
          ∀ k : Fin n, ‖coordinateDiffusion μ k (D.path t ω)‖ ≤ K := by
  let R := supportNormBound hμ
  have hR0 : 0 ≤ R := (supportNormBound_pos hμ).le
  have hR : ∀ x ∈ μ.support, ‖x‖ ≤ R := norm_le_supportNormBound hμ
  filter_upwards [D.ae_finite_horizon_covariance_det_lower_bound hμ hadm hℱ0 hnull]
    with ω hd T hT
  obtain ⟨δ, hδ, hdet⟩ := hd T hT
  obtain ⟨C, hC0, hC⟩ := exists_matrix_inverse_bound (n := n) (2*R^2) δ hδ
  refine ⟨(n : ℝ)*C*R+C+1, by positivity, ?_⟩
  intro t ht hlife
  exact coordinateCoefficients_bound_of_inverse hμ hadm.isotropic.affineSpan_support_eq_top
    (D.path t ω) hC0 hR0
    (hC (D.covariancePath t ω)
      (norm_covariance_le_of_support hμ hR0 hR (D.parameterPath t ω)) (hdet t ht hlife))
    (norm_mean_le_of_support hμ hR0 hR (D.parameterPath t ω))

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.ae_finite_horizon_coefficient_bound
