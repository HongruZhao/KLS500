import KLS.TraceDistributionMollification
import KLS.MomentMapMaximumPrinciple

open MeasureTheory Set Filter Metric ContinuousLinearMap Matrix
open scoped Topology ContDiff NNReal Convolution
noncomputable section
namespace KLS
variable {n : ℕ}

def translatedAverage (u : Space n → ℝ) (h x : Space n) : ℝ :=
  (u (x+h) + u (x-h)) / 2

lemma translatedAverage_contDiff {u : Space n → ℝ} {m : ℕ∞}
    (hu : ContDiff ℝ m u) (h : Space n) : ContDiff ℝ m (translatedAverage u h) := by
  unfold translatedAverage
  fun_prop

lemma convexOn_translatedAverage {u : Space n → ℝ}
    (hc : ConvexOn ℝ univ u) (h : Space n) : ConvexOn ℝ univ (translatedAverage u h) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  have hp := hc.2 (mem_univ (x+h)) (mem_univ (y+h)) ha hb hab
  have hm := hc.2 (mem_univ (x-h)) (mem_univ (y-h)) ha hb hab
  have hep : a • (x+h) + b • (y+h) = a • x + b • y + h := by
    rw [smul_add,smul_add,add_add_add_comm,← add_smul,hab,one_smul]
  have hem : a • (x-h) + b • (y-h) = a • x + b • y - h := by
    rw [smul_sub,smul_sub,sub_add_sub_comm,← add_smul,hab,one_smul]
  rw [hep] at hp
  rw [hem] at hm
  simp only [translatedAverage,smul_eq_mul] at *
  linarith

lemma coordinateHessian_translatedAverage {u : Space n → ℝ}
    (hu : ContDiff ℝ 2 u) (h x : Space n) :
    coordinateHessian (translatedAverage u h) x =
      (1/2 : ℝ) • (coordinateHessian u (x+h) + coordinateHessian u (x-h)) := by
  have hp : ContDiff ℝ 2 (fun y => u (y+h)) := by fun_prop
  have hm : ContDiff ℝ 2 (fun y => u (y-h)) := by fun_prop
  have he : translatedAverage u h = (1/2 : ℝ) • ((fun y => u (y+h)) + (fun y => u (y-h))) := by
    funext y
    simp only [translatedAverage,Pi.smul_apply,Pi.add_apply,smul_eq_mul]
    ring
  ext i j
  rw [he, coordinateHessian_smul (f := (fun y => u (y+h)) + (fun y => u (y-h)))
    (hp.add hm),coordinateHessian_add hp hm,
    coordinateHessian_translate hu]
  have hmn : (fun y => u (y-h)) = fun y => u (y + (-h)) := by funext y; rw [sub_eq_add_neg]
  rw [hmn,coordinateHessian_translate hu]
  simp only [Matrix.smul_apply,Matrix.add_apply,smul_eq_mul,sub_eq_add_neg]

/-- The genuine average of two shifted mollifications is strictly convex and
satisfies the nonlinear lower determinant bound with its averaged log-density. -/
theorem weak_moment_mollified_average_det_lower
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (k : ℕ) (h x : Space n) :
    (coordinateHessian (translatedAverage (mollify k u) h) x).PosDef ∧
      Real.exp (translatedAverage (mollify k (fun z => -u z + V (gradient u z))) h x) ≤
        (coordinateHessian (translatedAverage (mollify k u) h) x).det := by
  have hu : ContDiff ℝ 2 (mollify k u) := (mollify_contDiff hLip.continuous.locallyIntegrable k).of_le (by simp)
  apply posDef_and_exp_le_det_of_forall_trace
    (coordinateHessian_posSemidef_of_convex (translatedAverage_contDiff hu h)
      (convexOn_translatedAverage (convexOn_mollify hLip.continuous hc k) h) x)
  intro J hJ
  have hp := weak_moment_mollify_trace_bound hLip hc hV hK hKc hpush J hJ k (x+h)
  have hm := weak_moment_mollify_trace_bound hLip hc hV hK hKc hpush J hJ k (x-h)
  rw [coordinateHessian_translatedAverage hu,Matrix.mul_smul,Matrix.mul_add,
    Matrix.trace_smul,Matrix.trace_add]
  simp only [translatedAverage,smul_eq_mul]
  linarith

end KLS
end
