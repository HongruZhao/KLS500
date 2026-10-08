import KLS.AdaptiveEnergyIto
import KLS.TiltNumeratorDerivativeBounds
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Dimension-dependent bounds on genuine cumulant tensors, used only for
integrability of the energy process. No dimension-free inequality is used. -/
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

theorem normExponentialDomain_const_one_of_compact {μ : Measure (Space n)}
    [IsFiniteMeasure μ] (hμ : IsCompact μ.support) :
    NormExponentialDomain μ (fun _ => 1) := by
  refine ⟨aestronglyMeasurable_const, fun m a => ?_⟩
  exact integrable_of_continuous_compact_support_measure hμ (by fun_prop)

def isotropicMomentBound (n d : ℕ) : ℝ :=
  isotropicTailRadius n ^ d * geometricNormMomentConstant d

lemma isotropicMomentBound_nonneg (n d : ℕ) : 0 ≤ isotropicMomentBound n d :=
  mul_nonneg (pow_nonneg (isotropicTailRadius_pos n).le d)
    (geometricNormMomentConstant_pos d).le

/-- A finite Faà di Bruno sum; its order and dimension dependence is harmless
for the separate task of proving stochastic integrability. -/
def cumulantAprioriConstant (n m : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition m,
    ‖iteratedFDeriv ℝ c.length Real.log 1‖ * ∏ j, isotropicMomentBound n (c.partSize j)

lemma cumulantAprioriConstant_nonneg (n m : ℕ) : 0 ≤ cumulantAprioriConstant n m := by
  unfold cumulantAprioriConstant
  exact Finset.sum_nonneg fun c _ => mul_nonneg (norm_nonneg _)
    (Finset.prod_nonneg fun j _ => isotropicMomentBound_nonneg n _)

theorem norm_cumulantTensor_le_apriori {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    (hlc : measureLogConcave μ) (hiso : IsIsotropic μ) (m : ℕ) :
    ‖cumulantTensor μ m‖ ≤ cumulantAprioriConstant n m := by
  let Z := tiltNumerator μ (fun _ => 0) (fun _ => 1)
  have hZ : ContDiff ℝ (⊤ : ℕ∞) Z :=
    contDiff_tiltNumerator hμ continuous_const (integrable_const (1 : ℝ))
  have hZ0 : Z 0 = 1 := by simp [Z, tiltNumerator]
  have hlog : tiltLogLaplace μ = Real.log ∘ Z := by
    funext z
    simp [tiltLogLaplace, tiltPartition, Z, tiltNumerator]
  have hJ (d : ℕ) : ‖iteratedFDeriv ℝ d Z 0‖ ≤ isotropicMomentBound n d := by
    calc
      _ ≤ ∫ x, ‖(1 : ℝ)‖ * ‖x‖ ^ d ∂μ :=
        norm_iteratedFDeriv_tiltNumerator_le_moment
          (normExponentialDomain_const_one_of_compact hμ)
      _ = ∫ x, ‖x‖ ^ d ∂μ := by simp
      _ ≤ _ := hlc.isotropic_integral_norm_pow_le hiso d
  have hgl : ContDiffAt ℝ m Real.log (Z 0) := by
    rw [hZ0]
    exact Real.contDiffAt_log.mpr (by norm_num)
  unfold cumulantTensor
  rw [hlog, iteratedFDeriv_comp hgl (hZ.contDiffAt.of_le (by simp)) le_rfl, hZ0]
  unfold FormalMultilinearSeries.taylorComp cumulantAprioriConstant
  calc
    _ ≤ ∑ c : OrderedFinpartition m,
        ‖(ftaylorSeries ℝ Real.log 1).compAlongOrderedFinpartition (ftaylorSeries ℝ Z 0) c‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro c _
      apply (c.norm_compAlongOrderedFinpartition_le _ _).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hJ _)

end KLS
end
#print axioms KLS.norm_cumulantTensor_le_apriori
