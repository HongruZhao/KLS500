import KLS.CompactDirectionalCumulantBound
import KLS.DirectionalCumulantCompactTransfer

/-! The actual same-constant compact-cutoff passage gives the full original
class directional growth bound. The compact localization seed and actual
base estimate remain explicit hypotheses of this conditional result. -/
open MeasureTheory Set
open scoped BigOperators
noncomputable section
namespace KLS
open AdaptiveLocalization

theorem universalDirectionalCumulantBound_of_seed_and_base
    (hseed : ∀ n, UniformCompactMatrixSeed n)
    (hbase : ∀ n, CompactProcessEnergyBound n 1 (cumulantEnergyMajorant 144 1))
    {d : ℕ} (hd : 1 ≤ d) :
    UniversalDirectionalCumulantBound d (cumulantEnergyMajorant 144 d) := by
  apply universalDirectionalCumulantBound_of_compact
  intro n μ hμ hc u
  let := hμ.isProb
  exact directionalCumulantSquare_le_of_compactBound hc hμ.admissibleMeasure
    (compactCumulantEnergyBound_all_of_seed_and_base (hseed n) (hbase n) d hd) u

end KLS
end
