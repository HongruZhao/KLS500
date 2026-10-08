import KLS.WeakDerivativeMollification
import KLS.ConvexHessian
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Actual L2 finite differences and weak derivatives

The concrete mollifiers commute with actual translations and difference quotients.
Fatou controls their classical derivatives from the original difference quotients.
Weak Hilbert-space extraction then constructs an actual L2 distributional derivative.
-/

open MeasureTheory InnerProductSpace Set Filter ContinuousLinearMap
open scoped ContDiff ENNReal Convolution Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

def coordinateDifferenceQuotient (f : Space n → ℝ) (i : Fin n) (t : ℝ) : Space n → ℝ :=
  fun x => t⁻¹ * (f (x + t • EuclideanSpace.single i 1) - f x)

theorem memLp_coordinateDifferenceQuotient {f : Space n → ℝ}
    (hf : MemLp f 2 volume) (i : Fin n) (t : ℝ) :
    MemLp (coordinateDifferenceQuotient f i t) 2 volume := by
  have ht := hf.comp_measurePreserving
    (measurePreserving_add_right volume (t • EuclideanSpace.single i 1))
  exact (ht.sub hf).const_mul t⁻¹

theorem mollify_translate (f : Space n → ℝ) (k : ℕ) (a x : Space n) :
    mollify k (fun y => f (y + a)) x = mollify k f (x + a) := by
  have he (g : Space n → ℝ) (z : Space n) :
      mollify k g z = ∫ y, mollifierKernel n k y * g (z - y) := by
    unfold mollify scalarConvolution
    rw [convolution_symm (lsmul ℝ ℝ) (by ext; simp), convolution_def]
    rfl
  rw [he, he]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    apply congrArg (fun z => mollifierKernel n k y * f z)
    abel

theorem mollify_sub {f g : Space n → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (k : ℕ) : mollify k (f - g) = mollify k f - mollify k g := by
  funext x
  have hi (q : Space n → ℝ) (hq : MemLp q 2 volume) :
      Integrable (fun y => q y * mollifierKernel n k (x - y)) volume := by
    exact (mollifierKernel_hasCompactSupport k).convolutionExists_right
      (L := lsmul ℝ ℝ) (hq.locallyIntegrable (by norm_num))
      (mollifierKernel_contDiff k).continuous x
  unfold mollify scalarConvolution
  simp only [convolution_def, Pi.sub_apply, lsmul_apply, smul_eq_mul]
  simp_rw [sub_mul]
  exact integral_sub (hi f hf) (hi g hg)

theorem mollify_const_mul (c : ℝ) (f : Space n → ℝ) (k : ℕ) :
    mollify k (fun y => c * f y) = fun x => c * mollify k f x := by
  funext x
  unfold mollify scalarConvolution
  simp only [convolution_def, lsmul_apply, smul_eq_mul]
  simp_rw [mul_assoc]
  exact integral_const_mul c _

theorem mollify_coordinateDifferenceQuotient {f : Space n → ℝ}
    (hf : MemLp f 2 volume) (i : Fin n) (t : ℝ) (k : ℕ) :
    mollify k (coordinateDifferenceQuotient f i t) =
      coordinateDifferenceQuotient (mollify k f) i t := by
  have ht := hf.comp_measurePreserving
    (measurePreserving_add_right volume (t • EuclideanSpace.single i 1))
  change MemLp (fun y => f (y + t • EuclideanSpace.single i 1)) 2 volume at ht
  unfold coordinateDifferenceQuotient
  rw [mollify_const_mul]
  have hs := mollify_sub ht hf k
  funext x
  change t⁻¹ * mollify k ((fun y => f (y + t • EuclideanSpace.single i 1)) - f) x = _
  rw [hs]
  simp only [Pi.sub_apply, mollify_translate]

theorem tendsto_coordinateDifferenceQuotient {f : Space n → ℝ}
    (hf : Differentiable ℝ f) (i : Fin n) (x : Space n) :
    Tendsto (fun m => coordinateDifferenceQuotient f i (cutoffScale m) x)
      atTop (𝓝 (coordinateDerivative f i x)) := by
  have hfd : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • EuclideanSpace.single i 1) := by
    simpa only [zero_smul, add_zero] using (hf x).hasFDerivAt
  have hd := hfd.comp_hasDerivAt 0
    (hasDerivAt_affine_line x (EuclideanSpace.single i 1) 0)
  have hdz : HasDerivAt (fun t : ℝ => f (x + t • EuclideanSpace.single i 1))
      (coordinateDerivative f i x) 0 := by
    simpa only [zero_smul, add_zero, coordinateDerivative, Function.comp_def] using hd
  have hs : Tendsto cutoffScale atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨cutoffScale_tendsto_zero,
      Eventually.of_forall fun m => cutoffScale_pos m⟩
  simpa only [coordinateDifferenceQuotient, zero_add, zero_smul, add_zero, smul_eq_mul,
    Function.comp_def]
    using hdz.tendsto_slope_zero_right.comp hs

theorem eLpNorm_mollify_coordinateDerivative_le_of_difference_bound
    {f : Space n → ℝ} (hf : MemLp f 2 volume) (i : Fin n) {C : ℝ}
    (hbound : ∀ m, eLpNorm (coordinateDifferenceQuotient f i (cutoffScale m)) 2 volume ≤
      ENNReal.ofReal C) (k : ℕ) :
    eLpNorm (coordinateDerivative (mollify k f) i) 2 volume ≤ ENNReal.ofReal C := by
  have hm := mollify_contDiff (hf.locallyIntegrable (by norm_num)) k
  apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop)
    (f := fun m => coordinateDifferenceQuotient (mollify k f) i (cutoffScale m))
  · exact Eventually.of_forall fun m => by
      rw [← mollify_coordinateDifferenceQuotient hf]
      exact (eLpNorm_mollify_le (memLp_coordinateDifferenceQuotient hf i _) k).trans (hbound m)
  · exact fun m => (memLp_coordinateDifferenceQuotient (memLp_mollify hf k) i _).aestronglyMeasurable
  · exact (contDiff_coordinateDerivative hm (m := 0) (by simp) i).continuous.aestronglyMeasurable
  · exact Eventually.of_forall fun x => tendsto_coordinateDifferenceQuotient (hm.differentiable (by simp)) i x

theorem exists_weak_coordinateDerivative_of_difference_bound
    {f : Space n → ℝ} (hf : MemLp f 2 volume) (hc : HasCompactSupport f)
    (i : Fin n) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ m, eLpNorm (coordinateDifferenceQuotient f i (cutoffScale m)) 2 volume ≤
      ENNReal.ofReal C) :
    ∃ g : Lp ℝ 2 (volume : Measure (Space n)), ‖g‖ ≤ C ∧ HasWeakCoordinateDerivative f i g := by
  have hm (k : ℕ) := mollify_contDiff (hf.locallyIntegrable (by norm_num)) k
  have hd (k : ℕ) : MemLp (coordinateDerivative (mollify k f) i) 2 volume :=
    (contDiff_coordinateDerivative (hm k) (m := 0) (by simp) i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative (hasCompactSupport_mollify hc k) i)
  have he (k : ℕ) : (∫ x, coordinateDerivative (mollify k f) i x ^ 2) ≤ C ^ 2 := by
    rw [integral_sq_eq_toReal_eLpNorm_sq (hd k)]
    have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (eLpNorm_mollify_coordinateDerivative_le_of_difference_bound hf i hbound k)
    rw [ENNReal.toReal_ofReal hC] at hb
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg hb 2
  obtain ⟨g, hg, hweak⟩ := exists_weak_coordinateDerivative_of_approximation
    (f := fun k => mollify k f) (fun k => (hm k).of_le (by simp))
    (hasCompactSupport_mollify hc) hf (eLpNorm_mollify_sub_tendsto_zero hf) i (sq_nonneg C) he
  refine ⟨g, ?_, hweak⟩
  simpa only [Real.sqrt_sq hC] using hg

end KLS
end
