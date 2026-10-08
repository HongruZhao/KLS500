import OptCompactScalarSkew
import OptCubicMultilinear
import KLS.DirectionalWordSymmetry

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
noncomputable section
namespace KLS.ConstantReduction
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem cumulantTensor_three_symmetric (hμ : IsCompact μ.support)
    (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → Space n) :
    cumulantTensor μ 3 (v ∘ σ) = cumulantTensor μ 3 v :=
  smooth_iteratedFDeriv_comp_perm (contDiff_tiltLogLaplace hμ) v σ 0

theorem admissible_cumulantTensor_three_mixed_abs_le
    (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ) (x z : Space n) :
    |cumulantTensor μ 3 ![x,x,z]| ≤ 2 * ‖x‖^2 * ‖z‖ :=
  symmetric_cubic_multilinear_mixed_bound (cumulantTensor μ 3)
    (cumulantTensor_three_symmetric hμ)
    (admissible_cumulantTensor_three_diagonal_abs_le hμ hadm) x z

theorem admissible_cumulantTensor_three_slice_norm_le
    (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ) (x : Space n) :
    ‖curryCubic (cumulantTensor μ 3) x x‖ ≤ 2 * ‖x‖^2 :=
  symmetric_cubic_multilinear_slice_norm_le (cumulantTensor μ 3)
    (cumulantTensor_three_symmetric hμ) (by norm_num)
    (admissible_cumulantTensor_three_diagonal_abs_le hμ hadm) x

end KLS.ConstantReduction
end
