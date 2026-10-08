import KLS.FullQuadraticVarianceBound
import KLS.AdaptiveMatrixSeedTransfer
import KLS.CumulantEnergyBase
import KLS.CompactCumulantEnergyBound

/-! The actual compact rank-two cumulant slice retains the original
quadratic-eight bound, independently of any integrated-energy envelope. -/
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS
open AdaptiveLocalization

theorem compactCumulantEnergyBound_two_eight_unconditional {n : ℕ} :
    CompactCumulantEnergyBound n 2 8 := by
  intro μ hμ hadm u
  let := hadm.isProb
  have hlc : measureLogConcave (law μ (decodeState 0).1 (decodeState 0).2) := by
    simpa only [decodeState_zero, Prod.fst_zero, Prod.snd_zero, law_zero_zero] using hadm.logConcave
  have hseed := covarianceNoise_seed_eight_of_universal_quadratic hμ
    hadm.isotropic.affineSpan_support_eq_top 0 hlc
    (fun ν hν => hν.quadraticVarianceEight_unconditional)
  have hh := cumulantEnergy_two_le_eight_covariance hμ hadm.isotropic.affineSpan_support_eq_top u 0 hseed
  rw [← cumulantEnergy_one_eq_covariance hμ hadm.isotropic.affineSpan_support_eq_top u 0,
    cumulantEnergy_one_zero hμ hadm.isotropic u] at hh
  rw [cumulantEnergy_zero hadm.isotropic 2 u] at hh
  simpa only [cumulantSliceDirections] using hh

end KLS
end
