import KLS.LocalFamilyClippedContinuation

/-! A proved continuation criterion: bounded actual coefficients prevent finite lifetime. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
set_option maxHeartbeats 1000000
noncomputable section
namespace KLS.LocalDiffusion.LocalProcessFamily
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito LevyStochCalc.Ito.Picard
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {N d : ℕ} {W : MultidimBrownianMotion P d} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
  {b : (Fin N → ℝ) → Fin N → ℝ} {s : Fin d → (Fin N → ℝ) → Fin N → ℝ}
  (D : LocalProcessFamily W ℱ hW b s)

/-- This conclusion is derived from the actual original-coefficient equations,
continuous Brownian integral versions, and the genuine state-ball escape criterion. -/
theorem ae_lifetime_eq_top_of_coefficients_bounded
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (hb : ∀ᵐ ω ∂P, ∀ T : ℝ, 0 ≤ T → ∃ K : ℝ, 0 ≤ K ∧
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) T → (t : WithTop ℝ) < D.lifetime ω →
        ‖b (D.path t ω)‖ ≤ K ∧ ∀ k : Fin d, ‖s k (D.path t ω)‖ ≤ K) :
    ∀ᵐ ω ∂P, D.lifetime ω = ⊤ := by
  choose Z hZc hZ using fun L : ℕ => D.exists_continuous_clipped_representation hℱ0 hnull L
  filter_upwards [hb, D.ae_path_eq_of_le_exit, D.lifetime_pos, D.ae_finite_lifetime_escape,
    ae_all_iff.mpr hZ] with ω hbω hp hpos hescape hz
  by_contra hfinite
  obtain ⟨T, hT⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hT0 : 0 ≤ T := by
    rw [← hT] at hpos
    exact le_of_lt (by exact_mod_cast hpos)
  obtain ⟨K, hK0, hK⟩ := hbω T hT0
  obtain ⟨L, hL⟩ := exists_nat_gt K
  have hLR : K < D.coefficientClipRadius L := by
    unfold coefficientClipRadius
    linarith [norm_nonneg (D.coefficientVector 0)]
  have hagree (t : ℝ) (ht : 0 ≤ t) (hlife : (t : WithTop ℝ) < D.lifetime ω) :
      D.path t ω = Z L t ω := by
    obtain ⟨m, hm⟩ := (D.lt_lifetime_iff ω t).mp hlife
    have hcoef : (t : WithTop ℝ) < D.coefficientExit m L ω := by
      by_contra hn
      obtain ⟨u, hu, hhit⟩ := (Probability.exitTime_le_iff
        (D.continuous_coefficientVector.comp ((D m).pair.ito_Y.continuous_path ω))
        (D.coefficientClipRadius L) t).mp (le_of_not_gt hn)
      have huT : u ≤ T := by
        have htT : t < T := by rw [← hT] at hlife; exact_mod_cast hlife
        exact hu.2.trans htT.le
      have hule : (u : WithTop ℝ) ≤ (t : WithTop ℝ) := by exact_mod_cast hu.2
      have huE : (u : WithTop ℝ) ≤ D.exit m ω := hule.trans hm.le
      have hbound := hK u ⟨hu.1, huT⟩ (hule.trans_lt hlife)
      have hnorm : ‖D.coefficientVector (D.path u ω)‖ ≤ K := by
        change max ‖b (D.path u ω)‖ ‖fun k => s k (D.path u ω)‖ ≤ K
        exact max_le hbound.1 ((pi_norm_le_iff_of_nonneg hK0).mpr hbound.2)
      rw [hp m u hu.1 huE] at hnorm
      exact (not_le_of_gt hLR) (hhit.trans hnorm)
    exact hz L m t ht (le_min hm.le hcoef.le)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hZc L ω).continuousOn
  obtain ⟨t, ht, hlife, hlarge⟩ := hescape hfinite (B+1)
  have htT : t ≤ T := by
    rw [← hT] at hlife
    exact le_of_lt (by exact_mod_cast hlife)
  have hbound := hB t (show t ∈ Icc (0 : ℝ) T from ⟨ht, htT⟩)
  rw [← hagree t ht hlife] at hbound
  linarith

end KLS.LocalDiffusion.LocalProcessFamily
end
#print axioms KLS.LocalDiffusion.LocalProcessFamily.ae_lifetime_eq_top_of_coefficients_bounded
