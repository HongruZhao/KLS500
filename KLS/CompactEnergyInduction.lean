import KLS.CompactEnergyInductionStep

/-! Strong induction on genuine cumulant energies. The universal literal
matrix seed and the actual order-two process estimate are explicit inputs;
all higher-order lower-tensor estimates and induction steps are proved. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe

def UniformCompactMatrixSeed (n : ℕ) : Prop :=
  ∀ (μ : Measure (Space n)) [IsProbabilityMeasure μ], IsCompact μ.support → admissibleMeasure μ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : MultidimBrownianMotion P n)
      (D : MaximalProcess μ W (usualFiltration W) (usualFiltration_brownian W)),
      D.EnergyMatrixSeed

def CompactProcessEnergyBound (n r : ℕ) (B : ℝ) : Prop :=
  ∀ (μ : Measure (Space n)) [IsProbabilityMeasure μ], IsCompact μ.support → admissibleMeasure μ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : MultidimBrownianMotion P n)
      (D : MaximalProcess μ W (usualFiltration W) (usualFiltration_brownian W)) (u : Space n),
      cumulantEnergy μ r u 0 + (1/2 : ℝ) * D.integratedEnergy (r+1) u ≤ B * ‖u‖^2

theorem compactCumulantEnergyBound_of_processBound {n r : ℕ} {B : ℝ}
    (hB : CompactProcessEnergyBound n r B) : CompactCumulantEnergyBound n r B := by
  intro μ hμ hadm u
  let := hadm.isProb
  obtain ⟨Ω, mΩ, P, hP, W, D, _⟩ := exists_adaptiveGlobalProcess μ hμ hadm
  let := mΩ
  let := hP
  have hh := hB μ hμ hadm Ω P W D u
  have hn := D.integratedEnergy_nonnegative hμ hadm (r+1) u
  rw [cumulantEnergy_zero hadm.isotropic r u] at hh
  simp only [cumulantSliceDirections] at hh
  linarith

theorem compactProcessEnergyBound_all_of_seed_and_base {n : ℕ}
    (hseed : UniformCompactMatrixSeed n)
    (hbase : CompactProcessEnergyBound n 1 (cumulantEnergyMajorant 144 1)) :
    ∀ r, 1 ≤ r → CompactProcessEnergyBound n r (cumulantEnergyMajorant 144 r) := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr
    by_cases h1 : r = 1
    · simpa only [h1] using hbase
    have hr2 : 2 ≤ r := by omega
    intro μ inst hμ hadm Ω mΩ P instP W D u
    apply D.compact_energy_induction_step hμ hadm
      (usualFiltration_beforeZero W) (usualFiltration_null W) hr2 u
      (hseed μ hμ hadm Ω P W D)
    · intro j hj hlt
      exact compactCumulantEnergyBound_of_processBound (ih j hlt hj)
    · intro j hj hlt
      have hh := ih j hlt hj μ hμ hadm Ω P W D u
      have hn := cumulantEnergy_nonnegative (r := j) hμ hadm.isotropic.affineSpan_support_eq_top u 0
      linarith

theorem compactCumulantEnergyBound_all_of_seed_and_base {n : ℕ}
    (hseed : UniformCompactMatrixSeed n)
    (hbase : CompactProcessEnergyBound n 1 (cumulantEnergyMajorant 144 1)) :
    ∀ r, 1 ≤ r → CompactCumulantEnergyBound n r (cumulantEnergyMajorant 144 r) := by
  intro r hr
  exact compactCumulantEnergyBound_of_processBound
    (compactProcessEnergyBound_all_of_seed_and_base hseed hbase r hr)

end KLS.AdaptiveLocalization
end
