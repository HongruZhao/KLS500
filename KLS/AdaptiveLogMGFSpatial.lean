import KLS.AdaptiveLogMGFGenerator
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! Identification of the actual log-MGF Brownian coefficient with A^{-1/2}(gradient Lambda-a). -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.StandardLocalization
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem fderiv_tiltLogLaplace_apply (hμ : IsCompact μ.support) (w v : Space n) :
    fderiv ℝ (tiltLogLaplace μ) w v =
      tiltAverage μ (fun x => inner ℝ w x) (fun x => inner ℝ v x) := by
  have hp : HasDerivAt (fun u : ℝ => w+u•v) v 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w using 1 <;> simp
  have hd := ((contDiff_tiltLogLaplace hμ).differentiable (by simp) w).hasFDerivAt.comp_hasDerivAt_of_eq 0 hp (by simp)
  have hd' : HasDerivAt (fun u : ℝ => tiltLogLaplace μ (w+u•v))
      (fderiv ℝ (tiltLogLaplace μ) w v) 0 := by
    convert hd using 1
    funext u
    rfl
  have hl := hasDerivAt_log_tiltPartition hμ (q := fun x => inner ℝ w x)
    (s := fun x => inner ℝ v x) (by fun_prop) (by fun_prop) 0
  have he : (fun u : ℝ => tiltLogLaplace μ (w+u•v)) =
      fun u : ℝ => Real.log (tiltPartition μ (fun x => inner ℝ w x + u * inner ℝ v x)) := by
    funext u
    simp only [tiltLogLaplace, inner_add_left, inner_smul_left, RCLike.conj_to_real]
  rw [he] at hd'
  simpa only [zero_mul, add_zero] using hd'.unique hl

def inverseSqrtDirection (μ : Measure (Space n)) (z : Fin (n+n*n) → ℝ) (k : Fin n) : Space n :=
  toSpace (fun i => inverseSqrtCovariance μ (decodeState z) i k)

omit [IsProbabilityMeasure μ] in
theorem inner_inverseSqrtDirection (z : Fin (n+n*n) → ℝ) (k : Fin n) (x : Space n) :
    inner ℝ (inverseSqrtDirection μ z k) x = projection μ (decodeState z) k x :=
  inner_toSpace_eq _ _

omit [IsProbabilityMeasure μ] in
theorem coordinateLogMGF_eq_tiltLogLaplace (w : Space n) (z : Fin (n+n*n) → ℝ) :
    coordinateLogMGF μ w z = tiltLogLaplace (law μ (decodeState z).1 (decodeState z).2) w := rfl

/-- Actual Euclidean gradient of the log-Laplace transform, centered by the actual mean. -/
def spatialLogMGFDifference (μ : Measure (Space n)) (w : Space n) (z : Fin (n+n*n) → ℝ) : Space n :=
  gradient (tiltLogLaplace (law μ (decodeState z).1 (decodeState z).2)) w -
    toSpace (mean μ (decodeState z).1 (decodeState z).2)

def spatialLogMGFNoise (μ : Measure (Space n)) (w : Space n) (z : Fin (n+n*n) → ℝ) : Space n :=
  matrixAction (inverseSqrtCovariance μ (decodeState z)) (spatialLogMGFDifference μ w z)

theorem logMGFNoiseCoefficient_eq_spatial (hμ : IsCompact μ.support) (w : Space n)
    (k : Fin n) (z : Fin (n+n*n) → ℝ) :
    logMGFNoiseCoefficient μ w k z = spatialLogMGFNoise μ w z k := by
  let p := decodeState z
  let ν := law μ p.1 p.2
  let v := inverseSqrtDirection μ z k
  let M := coordinateAverage μ (exponentialObservable w) z
  let := law_isProbability hμ p.1 p.2
  have hν : IsCompact ν.support := by dsimp [ν]; rwa [support_law hμ]
  have hs : (fun x : Space n => inner ℝ v x) = projection μ p k :=
    funext (inner_inverseSqrtDirection z k)
  have hg : inner ℝ (gradient (tiltLogLaplace ν) w) v =
      coordinateAverage μ (fun x => exponentialObservable w x * projection μ p k x) z / M := by
    rw [inner_gradient_left, fderiv_tiltLogLaplace_apply hν, hs, tiltAverage_eq_ratio]
    change (∫ x, projection μ p k x * Real.exp (inner ℝ w x) ∂ν) /
        (∫ x, Real.exp (inner ℝ w x) ∂ν) = _
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    exact mul_comm _ _
  have hmean : inner ℝ (toSpace (mean μ p.1 p.2)) v =
      coordinateAverage μ (projection μ p k) z := by
    rw [real_inner_comm, inner_toSpace_eq]
    change (∑ i, inverseSqrtCovariance μ p i k * mean μ p.1 p.2 i) = _
    exact (average_projection hμ p k).symm
  have hnoise : logMGFNoiseCoefficient μ w k z = inner ℝ (spatialLogMGFDifference μ w z) v := by
    rw [logMGFNoiseCoefficient_eq_ratio hμ w, averageNoiseCoefficient,
      coordinateAverageGradient_apply hμ (integrable_exponentialObservable hμ w), coordinateScore_diffusion]
    change (_ - M * _) / M = inner ℝ (gradient (tiltLogLaplace ν) w - toSpace (mean μ p.1 p.2)) v
    rw [inner_sub_left, hg, hmean]
    have hM : M ≠ 0 := (coordinateMGF_pos hμ w z).ne'
    field_simp
    rfl
  rw [hnoise]
  unfold spatialLogMGFNoise
  rw [real_inner_comm, inner_inverseSqrtDirection, matrixAction_apply]
  unfold projection
  apply Finset.sum_congr rfl
  intro i _
  have hsym := congrFun (congrFun (inverseSqrtCovariance_isSymm (μ := μ) p).eq k) i
  change inverseSqrtCovariance μ p i k * _ = inverseSqrtCovariance μ p k i * _
  exact congrArg (fun a : ℝ => a * (spatialLogMGFDifference μ w z) i) hsym

/-- The finite coordinate square contraction is the actual Euclidean norm in (71). -/
theorem logMGFDrift_eq_spatial_norm (hμ : IsCompact μ.support) (w : Space n)
    (z : Fin (n+n*n) → ℝ) :
    logMGFDrift μ w z = -(1/2) * ‖spatialLogMGFNoise μ w z‖^2 := by
  unfold logMGFDrift
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [logMGFNoiseCoefficient_eq_spatial hμ w]

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.logMGFNoiseCoefficient_eq_spatial
#print axioms KLS.AdaptiveLocalization.logMGFDrift_eq_spatial_norm
