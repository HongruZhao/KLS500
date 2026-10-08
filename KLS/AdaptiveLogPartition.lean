import KLS.AdaptiveLogMGFDriftIntegrability
import KLS.DirectionalWordSymmetry

/-! Smooth actual state log-partition and the spatial translation formula for log-MGF. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.StandardLocalization KLS.FiniteFeatureTilt
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def coordinatePartition (μ : Measure (Space n)) (z : Fin (n+n*n) → ℝ) : ℝ :=
  tiltPartition μ (exponent (decodeState z).1 (decodeState z).2)

def coordinateLogPartition (μ : Measure (Space n)) (z : Fin (n+n*n) → ℝ) : ℝ :=
  Real.log (coordinatePartition μ z)

theorem coordinatePartition_pos (hμ : IsCompact μ.support) (z : Fin (n+n*n) → ℝ) :
    0 < coordinatePartition μ z := tiltPartition_pos hμ (continuous_exponent _ _)

theorem contDiff_coordinatePartition (hμ : IsCompact μ.support) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinatePartition μ) := by
  have h := (contDiff_featureNumerator hμ continuous_feature (q := fun _ => 0)
    continuous_const (integrable_const (1 : ℝ))).comp (contDiff_parameter.comp contDiff_decodeState)
  convert h using 1
  funext z
  simp only [coordinatePartition, featureNumerator, tiltPartition, one_mul, zero_add]
  congr 1
  funext x
  rw [exponent_eq_feature_inner]
  simp only [Function.comp_apply, one_mul, zero_add]

theorem contDiff_coordinateLogPartition (hμ : IsCompact μ.support) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateLogPartition μ) :=
  (contDiff_coordinatePartition hμ).log (fun z => (coordinatePartition_pos hμ z).ne')

/-- Continuous linear embedding of spatial tilts into the actual linear coefficients. -/
def linearStateCLM : Space n →L[ℝ] (Fin (n+n*n) → ℝ) :=
  ContinuousLinearMap.pi (Fin.addCases (fun i => EuclideanSpace.proj i) (fun _ => 0))

omit [IsProbabilityMeasure μ] in
theorem coordinateScore_linearState (w x : Space n) :
    coordinateScore (linearStateCLM w) x = inner ℝ w x := by
  simp only [coordinateScore, decodeState, linearStateCLM, ContinuousLinearMap.pi_apply,
    Fin.addCases_left, Fin.addCases_right, _root_.zero_apply,
    exponent, zero_mul, Finset.sum_const_zero, zero_div, sub_zero]
  rw [inner_eq_coordinate_sum]
  apply Finset.sum_congr rfl
  intro i _
  change w i * x i = x i * w i
  ring

omit [IsProbabilityMeasure μ] in
theorem exponent_state_add_linear (z : Fin (n+n*n) → ℝ) (w x : Space n) :
    exponent (decodeState (z+linearStateCLM w)).1 (decodeState (z+linearStateCLM w)).2 x =
      exponent (decodeState z).1 (decodeState z).2 x + inner ℝ w x := by
  have h := congrFun (coordinate_exponent_line z (linearStateCLM w) (1 : ℝ)) x
  simpa only [one_smul, one_mul, coordinateScore_linearState] using h

/-- The actual normalized MGF is the log-partition difference under a spatial state shift. -/
theorem coordinateLogMGF_eq_partition_difference (hμ : IsCompact μ.support)
    (z : Fin (n+n*n) → ℝ) (w : Space n) :
    coordinateLogMGF μ w z = coordinateLogPartition μ (z+linearStateCLM w) - coordinateLogPartition μ z := by
  change Real.log (∫ x, Real.exp (inner ℝ w x) ∂μ.tilted
    (exponent (decodeState z).1 (decodeState z).2)) = _
  rw [integral_exp_tilted]
  have he : (fun x => exponent (decodeState z).1 (decodeState z).2 x + inner ℝ w x) =
      exponent (decodeState (z+linearStateCLM w)).1 (decodeState (z+linearStateCLM w)).2 := by
    funext x
    exact (exponent_state_add_linear z w x).symm
  change Real.log ((∫ x, Real.exp ((fun x => exponent (decodeState z).1 (decodeState z).2 x + inner ℝ w x) x) ∂μ) / _) = _
  rw [he]
  exact Real.log_div (coordinatePartition_pos hμ (z+linearStateCLM w)).ne' (coordinatePartition_pos hμ z).ne'

/-- All-order joint smoothness is proved before any spatial-state differentiation is interchanged. -/
theorem contDiff_coordinateLogMGF_joint (hμ : IsCompact μ.support) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : (Fin (n+n*n) → ℝ) × Space n => coordinateLogMGF μ p.2 p.1) := by
  simp_rw [coordinateLogMGF_eq_partition_difference hμ]
  exact ((contDiff_coordinateLogPartition hμ).comp
    (contDiff_fst.add (linearStateCLM.contDiff.comp contDiff_snd))).sub
    ((contDiff_coordinateLogPartition hμ).comp contDiff_fst)

omit [IsProbabilityMeasure μ] in
theorem linearState_inverseSqrtDirection (z : Fin (n+n*n) → ℝ) (k : Fin n) :
    linearStateCLM (inverseSqrtDirection μ z k) = coordinateDiffusion μ k z := by
  funext a
  refine Fin.addCases ?_ ?_ a
  · intro i
    simp only [linearStateCLM, ContinuousLinearMap.pi_apply, Fin.addCases_left,
      coordinateDiffusion, diffusion, encodeState]
    rfl
  · intro ij
    simp only [linearStateCLM, ContinuousLinearMap.pi_apply, Fin.addCases_right,
      coordinateDiffusion, diffusion, encodeState, _root_.zero_apply]
    rfl

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.contDiff_coordinateLogMGF_joint
#print axioms KLS.AdaptiveLocalization.coordinateLogMGF_eq_partition_difference
