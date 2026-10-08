import KLS.ConvexMollifierProperties
import KLS.WeakMomentTraceDistribution
import KLS.MatrixLogDetTraceClosure

open MeasureTheory Set Filter Metric ContinuousLinearMap Matrix
open scoped Topology ContDiff NNReal Convolution
noncomputable section
namespace KLS
variable {n : ℕ}

lemma trace_hessian_scalarConvolution {u κ : Space n → ℝ}
    (hu : LocallyIntegrable u volume) (hκ : ContDiff ℝ 2 κ)
    (hc : HasCompactSupport κ) (J : Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    (J * coordinateHessian (scalarConvolution u κ) x).trace =
      ∫ y, u y * (J * coordinateHessian κ (x-y)).trace := by
  have hi (i j : Fin n) : Integrable (fun y => u y * (J i j * coordinateHessian κ (x-y) j i)) := by
    have hh := (hasCompactSupport_coordinateHessian hc j i).convolutionExists_right (lsmul ℝ ℝ)
      hu (contDiff_coordinateHessian hκ (m := 0) (by norm_num) j i).continuous x
    convert hh.const_mul (J i j) using 1
    funext y
    change u y * (J i j * coordinateHessian κ (x-y) j i) =
      J i j * (u y * coordinateHessian κ (x-y) j i)
    ring
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [coordinateHessian_scalarConvolution hu hκ hc]
  rw [show (fun y => u y * (J i j * coordinateHessian κ (x-y) j i)) =
      (fun y => J i j * (u y * coordinateHessian κ (x-y) j i)) by funext y; ring,
    integral_const_mul]
  rfl

/-- Testing a distribution inequality against the genuine reflected mollifier
produces the corresponding classical trace inequality. -/
theorem mollify_le_trace_hessian_of_distribution
    {u f : Space n → ℝ} (hu : Continuous u)
    (J : Matrix (Fin n) (Fin n) ℝ)
    (hd : ∀ χ : Space n → ℝ, ContDiff ℝ 2 χ → HasCompactSupport χ →
      (∀ y, 0 ≤ χ y) → (∫ y, f y * χ y) ≤ ∫ y, u y * (J * coordinateHessian χ y).trace)
    (k : ℕ) (x : Space n) :
    mollify k f x ≤ (J * coordinateHessian (mollify k u) x).trace := by
  let χ := fun y => mollifierKernel n k (x-y)
  have hκ : ContDiff ℝ 2 (mollifierKernel n k) := (mollifierKernel_contDiff k).of_le (by simp)
  have hχ : ContDiff ℝ 2 χ := hκ.comp (contDiff_const.sub contDiff_id)
  have hh := hd χ hχ ((mollifierKernel_hasCompactSupport k).comp_homeomorph (Homeomorph.subLeft x))
    (fun y => (mollifierBump n k).nonneg_normed (x-y))
  change scalarConvolution f (mollifierKernel n k) x ≤
    (J * coordinateHessian (scalarConvolution u (mollifierKernel n k)) x).trace
  rw [trace_hessian_scalarConvolution hu.locallyIntegrable hκ
    (mollifierKernel_hasCompactSupport k)]
  calc
    _ ≤ ∫ y, u y * (J * coordinateHessian χ y).trace := hh
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        have he : coordinateHessian χ y = coordinateHessian (mollifierKernel n k) (x-y) := by
          ext i j
          exact coordinateHessian_const_sub hκ x y i j
        dsimp only
        rw [he]

/-- Actual weak moment data give every trace inequality for each smooth
mollification, with the actual mollified log-density. -/
theorem weak_moment_mollify_trace_bound
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (J : Matrix (Fin n) (Fin n) ℝ) (hJ : J.PosDef) (k : ℕ) (x : Space n) :
    mollify k (fun z => -u z + V (gradient u z)) x + Real.log J.det + n ≤
      (J * coordinateHessian (mollify k u) x).trace := by
  have hg := continuous_gradient_of_subsingleton_convexSubgradient hLip hc
    (moment_convexSubgradient_subsingleton_closedTarget hLip hc hV hK hKc hpush)
  have hf : Continuous (fun z => -u z + V (gradient u z)) :=
    hLip.continuous.neg.add (hV.comp hg)
  have hh := mollify_le_trace_hessian_of_distribution hLip.continuous J
    (fun χ hχ hχc hχ0 => weak_moment_distribution_trace_bound
      hLip hc hV hK hKc hpush J hJ hχ hχc hχ0) k x
  rw [show (fun z => -u z + V (gradient u z) + Real.log J.det + n) =
    (fun z => (-u z + V (gradient u z)) + (Real.log J.det + n)) by funext z; ring,
    mollify_add_const hf] at hh
  simpa only [add_assoc] using hh

end KLS
end
