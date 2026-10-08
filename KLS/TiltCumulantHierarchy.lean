import KLS.TiltFrechet

/-!
# All-order cumulant tensors and their exact tilt hierarchy

Cumulants are the actual iterated Fréchet derivatives at zero of the logarithm
of the Laplace transform. Compact support proves smoothness first. The tilt
translation formula then identifies every cumulant at every tilted law and
proves its full Fréchet derivative, including mixed directional evaluations.
These are deterministic identities; no stochastic differential is asserted.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff

noncomputable section
namespace KLS

def cumulantTensor {n : ℕ} (μ : Measure (Space n)) (m : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin m => Space n) ℝ :=
  iteratedFDeriv ℝ m (tiltLogLaplace μ) 0

theorem tiltLogLaplace_exponentialTilt {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) (z w : Space n) :
    tiltLogLaplace (exponentialTilt μ z) w =
      tiltLogLaplace μ (z + w) - tiltLogLaplace μ z := by
  unfold tiltLogLaplace tiltPartition exponentialTilt
  rw [integral_exp_tilted]
  simp only [Pi.add_apply, ← inner_add_left]
  exact Real.log_div (tiltPartition_pos hμ (q := fun x => inner ℝ (z + w) x)
    (by fun_prop)).ne' (tiltPartition_pos hμ (q := fun x => inner ℝ z x) (by fun_prop)).ne'

theorem cumulantTensor_exponentialTilt {n m : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) (hm : m ≠ 0) (z : Space n) :
    cumulantTensor (exponentialTilt μ z) m = iteratedFDeriv ℝ m (tiltLogLaplace μ) z := by
  unfold cumulantTensor
  have he : tiltLogLaplace (exponentialTilt μ z) =
      fun w => tiltLogLaplace μ (z + w) - tiltLogLaplace μ z :=
    funext (tiltLogLaplace_exponentialTilt hμ z)
  rw [he]
  have hc : ContDiffAt ℝ m (fun w => tiltLogLaplace μ (z + w)) 0 :=
    ((contDiff_tiltLogLaplace hμ).comp (contDiff_const.add contDiff_id)).contDiffAt.of_le
      (by simp)
  rw [fun_iteratedFDeriv_sub_apply hc contDiffAt_const,
    iteratedFDeriv_const_of_ne hm, Pi.zero_apply, sub_zero,
    iteratedFDeriv_comp_add_left, add_zero]

theorem hasFDerivAt_cumulantTensor_exponentialTilt {n m : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    (hm : m ≠ 0) (z : Space n) :
    HasFDerivAt (fun w => cumulantTensor (exponentialTilt μ w) m)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Space n) ℝ
        (cumulantTensor (exponentialTilt μ z) (m + 1))) z := by
  simp_rw [cumulantTensor_exponentialTilt hμ hm]
  rw [cumulantTensor_exponentialTilt hμ (Nat.succ_ne_zero m)]
  have hc : ContDiff ℝ (m + 1 : ℕ) (tiltLogLaplace μ) :=
    (contDiff_tiltLogLaplace hμ).of_le (by simp)
  have hm' : (m : ℕ∞ω) < ((m + 1 : ℕ) : ℕ∞ω) := by exact_mod_cast Nat.lt_succ_self m
  have hd := (ContDiff.differentiable_iteratedFDeriv hm' hc z).hasFDerivAt
  simpa only [fderiv_iteratedFDeriv, Function.comp_apply] using hd

theorem hasDerivAt_cumulantTensor_exponentialTilt_eval {n m : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    (hm : m ≠ 0) (z v : Space n) (h : Fin m → Space n) (t : ℝ) :
    HasDerivAt (fun u : ℝ => cumulantTensor (exponentialTilt μ (z + u • v)) m h)
      (cumulantTensor (exponentialTilt μ (z + t • v)) (m + 1) (Fin.cons v h)) t := by
  have ht : HasDerivAt (fun u : ℝ => z + u • v) v t := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const v).const_add z
  have hd0 := hasFDerivAt_cumulantTensor_exponentialTilt hμ hm (z + t • v)
  have hd := (hd0.continuousMultilinear_apply_const h).comp_hasDerivAt t ht
  simpa only [Function.comp_def, ContinuousLinearMap.flipMultilinear_apply_apply,
    continuousMultilinearCurryLeftEquiv_apply] using hd

end KLS
end

#print axioms KLS.tiltLogLaplace_exponentialTilt
#print axioms KLS.cumulantTensor_exponentialTilt
#print axioms KLS.hasFDerivAt_cumulantTensor_exponentialTilt
#print axioms KLS.hasDerivAt_cumulantTensor_exponentialTilt_eval
