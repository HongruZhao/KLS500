import KLS.AdaptiveCumulantGenerator
import KLS.DirectionalWordLeibniz

/-! Actual next cumulants in every spatial word of the log-MGF noise. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS

/-- Evaluation of the actual cumulant tensor on a finite ordered list. -/
def listCumulant {n : ℕ} (μ : Measure (Space n)) (vs : List (Space n)) : ℝ :=
  cumulantTensor μ vs.length vs.get

namespace AdaptiveLocalization
open KLS.StandardLocalization
variable {n m : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem listCumulant_law_eq_word (hμ : IsCompact μ.support) (vs : List (Space n))
    (hne : vs ≠ []) (z : Fin (n+n*n) → ℝ) :
    listCumulant (law μ (decodeState z).1 (decodeState z).2) vs =
      directionalWordDerivative (coordinateLogPartition μ) (vs.map linearStateCLM) z := by
  have hm : vs.length ≠ 0 := by simpa using hne
  have he := coordinateCumulant_eq_word hμ hm vs.get z
  simpa only [coordinateCumulant, listCumulant, List.ofFn_get] using he

theorem logMGFNoiseCoefficient_eq_partition_word (hμ : IsCompact μ.support)
    (z : Fin (n+n*n) → ℝ) (k : Fin n) (w : Space n) :
    logMGFNoiseCoefficient μ w k z =
      directionalWordDerivative (coordinateLogPartition μ) [coordinateDiffusion μ k z]
        (z+linearStateCLM w) -
      directionalWordDerivative (coordinateLogPartition μ) [coordinateDiffusion μ k z] z :=
  coordinateLogMGF_word hμ w [coordinateDiffusion μ k z] z

theorem contDiff_logMGFNoiseCoefficient_spatial (hμ : IsCompact μ.support)
    (z : Fin (n+n*n) → ℝ) (k : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w => logMGFNoiseCoefficient μ w k z) := by
  simp_rw [logMGFNoiseCoefficient_eq_partition_word hμ]
  exact ((contDiff_directionalWordDerivative (contDiff_coordinateLogPartition hμ) _).comp
    (contDiff_const.add linearStateCLM.contDiff)).sub contDiff_const

/-- A zero-length word vanishes because the centered log-MGF noise is zero at the origin. -/
def cumulantNoiseWord (μ : Measure (Space n)) (z : Fin (n+n*n) → ℝ)
    (k : Fin n) (vs : List (Space n)) : ℝ :=
  if vs = [] then 0 else listCumulant (law μ (decodeState z).1 (decodeState z).2)
    (inverseSqrtDirection μ z k :: vs)

theorem logMGFNoiseCoefficient_word_zero (hμ : IsCompact μ.support)
    (z : Fin (n+n*n) → ℝ) (k : Fin n) (vs : List (Space n)) :
    directionalWordDerivative (fun w => logMGFNoiseCoefficient μ w k z) vs 0 =
      cumulantNoiseWord μ z k vs := by
  by_cases hne : vs = []
  · subst vs
    simp only [directionalWordDerivative_nil, logMGFNoiseCoefficient_eq_partition_word hμ,
      map_zero, add_zero, sub_self, cumulantNoiseWord, ite_true]
  · have he : (fun w => logMGFNoiseCoefficient μ w k z) = fun w =>
        directionalWordDerivative (coordinateLogPartition μ) [coordinateDiffusion μ k z]
          (z+linearStateCLM w) -
        directionalWordDerivative (coordinateLogPartition μ) [coordinateDiffusion μ k z] z :=
      funext (logMGFNoiseCoefficient_eq_partition_word hμ z k)
    rw [he]
    have hf := contDiff_coordinateLogPartition hμ
    have hD := contDiff_directionalWordDerivative hf [coordinateDiffusion μ k z]
    have hs : ContDiff ℝ (⊤ : ℕ∞) (fun w : Space n =>
        directionalWordDerivative (coordinateLogPartition μ) [coordinateDiffusion μ k z]
          (z+linearStateCLM w)) := hD.comp (contDiff_const.add linearStateCLM.contDiff)
    rw [directionalWordDerivative_sub hs contDiff_const,
      directionalWordDerivative_const_of_ne_nil _ _ hne]
    simp only [Pi.zero_apply, sub_zero]
    rw [directionalWordDerivative_comp_affine hD]
    simp only [map_zero, add_zero]
    rw [directionalWordDerivative_append]
    simp only [cumulantNoiseWord, hne, ite_false]
    rw [listCumulant_law_eq_word hμ _ (by simp)]
    simp only [List.map_cons, linearState_inverseSqrtDirection]
    exact congrFun (directionalWordDerivative_perm hf List.perm_append_comm) z

/-- Full labeled-subset Leibniz drift, with both empty factors correctly zero.
This is the exact all-order quadratic drift before pairing complementary subsets. -/
theorem cumulantGenerator_eq_mask_sum (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hm : m ≠ 0) (h : Fin m → Space n)
    (z : Fin (n+n*n) → ℝ) :
    cumulantGenerator μ m h z = -(1/2) * ∑ k : Fin n, ∑ s : Fin m → Bool,
      cumulantNoiseWord μ z k (maskedDirections h s) *
        cumulantNoiseWord μ z k (maskedDirections h (fun i => !(s i))) := by
  rw [cumulantGenerator_eq_spatial_derivative hμ hfull hm]
  have hq (k : Fin n) := contDiff_logMGFNoiseCoefficient_spatial hμ z k
  change directionalWordDerivative (fun w => -(1/2) * ∑ k : Fin n,
    (logMGFNoiseCoefficient μ w k z)^2) (List.ofFn h) 0 = _
  rw [directionalWordDerivative_const_mul (ContDiff.sum fun k _ => (hq k).pow 2),
    directionalWordDerivative_sum _ (fun k _ => (hq k).pow 2)]
  simp only [pow_two]
  simp_rw [directionalWordDerivative_mul_masks (hq _) (hq _),
    logMGFNoiseCoefficient_word_zero hμ]

end AdaptiveLocalization
end KLS
end
#print axioms KLS.AdaptiveLocalization.cumulantGenerator_eq_mask_sum
