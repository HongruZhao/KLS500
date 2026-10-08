import KLS.LocalFamilyClippedEquation

/-! Continuous global processes constructed from clipped original coefficients. -/
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

theorem exists_continuous_clipped_representation
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A) (L : ℕ) :
    ∃ Z : ℝ → Ω → Fin N → ℝ,
      (∀ ω : Ω, Continuous fun t => Z t ω) ∧
      (∀ᵐ ω ∂P, ∀ m : ℕ, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) ≤ D.jointCoefficientExit m L ω →
        D.path t ω = Z t ω) := by
  have hex (i : Fin N) (k : Fin d) : ∃ M : ℝ → Ω → ℝ,
      (∀ ω : Ω, Continuous fun t => M t ω) ∧ (∀ t : ℝ, Measurable[ℱ t] (M t)) ∧
      ∀ t : ℝ, 0 ≤ t → M t =ᵐ[P] D.clippedNoiseIntegral L i k t :=
    exists_continuousAdapted_modification (W.W k) ℱ (hW k) (D.clippedNoise L i k)
      (D.clippedNoise_measurable L i k) (D.clippedNoise_progressive L i k)
      (D.clippedNoise_energy L i k) (D.coefficientClipRadius_nonneg L) (D.clippedNoise_bound L i k)
      hℱ0 hnull
  choose M hMc hMa hMe using hex
  let Z : ℝ → Ω → Fin N → ℝ := fun t ω i =>
    (∫ u in Icc (0 : ℝ) t, D.clippedDrift L i ω u ∂volume) + ∑ k : Fin d, M i k t ω
  have hZc (ω : Ω) : Continuous fun t => Z t ω := by
    apply continuous_pi
    intro i
    exact (continuous_setIntegral_Icc (Measurable.of_uncurry_left (D.clippedDrift_measurable L i))
      (D.coefficientClipRadius_nonneg L) (D.clippedDrift_bound L i ω)).add
        (continuous_finsetSum _ fun k _ => hMc i k ω)
  have hZm (T : ℝ) (hT : 0 ≤ T) : ∀ᵐ ω ∂P, ∀ i : Fin N,
      Z T ω i = (∫ t in Icc (0 : ℝ) T, D.clippedDrift L i ω t ∂volume) +
        ∑ k : Fin d, D.clippedNoiseIntegral L i k T ω := by
    filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr fun k => hMe i k T hT] with ω hω i
    exact congrArg (fun a : ℝ => (∫ t in Icc (0 : ℝ) T, D.clippedDrift L i ω t ∂volume) + a)
      (Finset.sum_congr rfl fun k _ => hω i k)
  have hM0 : ∀ᵐ ω ∂P, ∀ (i : Fin N) (k : Fin d), M i k 0 ω = 0 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro k
    have hz := stochasticIntegralBrownian_ae_zero_of_nonpos (W.W k) ℱ (hW k)
      (D.clippedNoise L i k) (D.clippedNoise_measurable L i k)
      (D.clippedNoise_progressive L i k) (D.clippedNoise_energy L i k) (show (0 : ℝ) ≤ 0 from le_rfl)
    filter_upwards [hMe i k 0 le_rfl, hz] with ω he hzω
    exact he.trans hzω
  have hZ0 : Z 0 =ᵐ[P] fun _ => 0 := by
    filter_upwards [hM0] with ω hω
    funext i
    simp [Z, hω]
  have hlocal (m : ℕ) : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) ≤ D.jointCoefficientExit m L ω →
      (D m).pair.Y t ω = Z t ω := by
    apply ae_all_eq_before_cutoff ((D m).pair.ito_Y.continuous_path) hZc
    · filter_upwards [(D m).initial_Y, hZ0] with ω h0 hz
      exact h0.trans hz.symm
    · intro T hT
      filter_upwards [D.clipped_equation_before_joint m L hT, D.ae_path_eq_of_le_exit, hZm T hT.le]
        with ω he hp hz hle
      rw [← hp m T hT.le (le_min_iff.mp hle).1]
      funext i
      exact (he hle i).trans (hz i).symm
  refine ⟨Z, hZc, ?_⟩
  filter_upwards [ae_all_iff.mpr hlocal, D.ae_path_eq_of_le_exit] with ω hl hp m t ht he
  rw [hp m t ht (le_min_iff.mp he).1]
  exact hl m t ht he

end KLS.LocalDiffusion.LocalProcessFamily
end
#print axioms KLS.LocalDiffusion.LocalProcessFamily.exists_continuous_clipped_representation
