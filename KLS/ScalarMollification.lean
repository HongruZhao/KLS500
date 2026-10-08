import KLS.WeightedLocalDistribution
import KLS.ProbabilityKernelConvolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Actual scalar mollification and its derivatives

The kernels are concrete normalized smooth bumps with radii tending to zero.
Convolution produces smooth functions, converges almost everywhere for locally
integrable inputs, and contracts L² for globally L² inputs. Coordinate
Fréchet derivatives of convolution are identified with convolution against the
actual kernel derivatives.
-/

open MeasureTheory InnerProductSpace Set Filter ContinuousLinearMap
open scoped ContDiff ENNReal Convolution Topology

noncomputable section
namespace KLS

variable {n : ℕ}

/-- Scalar Lebesgue convolution. -/
def scalarConvolution (f κ : Space n → ℝ) : Space n → ℝ :=
  f ⋆[lsmul ℝ ℝ, volume] κ

/-- Shrinking concrete smooth bumps; the outer radius is twice the inner radius. -/
def mollifierBump (n k : ℕ) : ContDiffBump (0 : Space n) :=
  ⟨cutoffScale k, 2 * cutoffScale k, cutoffScale_pos k, by nlinarith [cutoffScale_pos k]⟩

def mollifierKernel (n k : ℕ) : Space n → ℝ := (mollifierBump n k).normed volume

def mollify (k : ℕ) (f : Space n → ℝ) : Space n → ℝ :=
  scalarConvolution f (mollifierKernel n k)

lemma mollifierKernel_contDiff (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (mollifierKernel n k) :=
  (mollifierBump n k).contDiff_normed

lemma mollifierKernel_hasCompactSupport (k : ℕ) : HasCompactSupport (mollifierKernel n k) :=
  (mollifierBump n k).hasCompactSupport_normed

/-- Every mollification of a locally integrable function is genuinely smooth. -/
theorem mollify_contDiff {f : Space n → ℝ} (hf : LocallyIntegrable f volume) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (mollify k f) :=
  (mollifierKernel_hasCompactSupport k).contDiff_convolution_right (lsmul ℝ ℝ) hf
    (mollifierKernel_contDiff k)

/-- These actual mollifications converge almost everywhere to their locally integrable input. -/
theorem mollify_tendsto_ae {f : Space n → ℝ} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x ∂volume, Tendsto (fun k => mollify k f x) atTop (𝓝 (f x)) := by
  have hr : Tendsto (fun k => (mollifierBump n k).rOut) atTop (𝓝 0) := by
    simpa only [mollifierBump, mul_zero] using cutoffScale_tendsto_zero.const_mul 2
  have hb : ∀ᶠ k in atTop, (mollifierBump n k).rOut ≤ 2 * (mollifierBump n k).rIn :=
    Eventually.of_forall fun _ => le_rfl
  have he := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hr hb hf
  have heq (k : ℕ) : mollify k f =
      (mollifierBump n k).normed volume ⋆[lsmul ℝ ℝ, volume] f := by
    unfold mollify scalarConvolution mollifierKernel
    exact convolution_symm (lsmul ℝ ℝ) (by ext; simp)
  simpa only [heq] using he

/-- The concrete mollifiers have a uniform L² bound. -/
theorem eLpNorm_mollify_le {f : Space n → ℝ} (hf : MemLp f 2 volume) (k : ℕ) :
    eLpNorm (mollify k f) 2 volume ≤ eLpNorm f 2 volume := by
  have he := ProbabilityKernel.eLpNorm_convolution_le (p := 2) (by norm_num)
    (fun x => (mollifierBump n k).nonneg_normed x)
    ((mollifierBump n k).continuous_normed.aestronglyMeasurable)
    (mollifierBump n k).integral_normed (by simpa using hf)
  simpa only [ENNReal.ofReal_ofNat, mollify, scalarConvolution, mollifierKernel] using he

/-- Derivatives of a scalar convolution are actual convolutions with kernel derivatives. -/
theorem coordinateDerivative_scalarConvolution {f κ : Space n → ℝ}
    (hf : LocallyIntegrable f volume) (hκ : ContDiff ℝ 1 κ)
    (hc : HasCompactSupport κ) (i : Fin n) (x : Space n) :
    coordinateDerivative (scalarConvolution f κ) i x =
      scalarConvolution f (coordinateDerivative κ i) x := by
  unfold coordinateDerivative scalarConvolution
  rw [(hc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hf hκ x).fderiv]
  exact convolution_precompR_apply (lsmul ℝ ℝ) hf (hc.fderiv ℝ)
    (hκ.continuous_fderiv (by norm_num)) x (EuclideanSpace.single i 1)

/-- Reflection changes the sign of the actual first coordinate derivative. -/
theorem coordinateDerivative_const_sub {f : Space n → ℝ} (hf : Differentiable ℝ f)
    (a x : Space n) (i : Fin n) :
    coordinateDerivative (fun y => f (a - y)) i x = -coordinateDerivative f i (a - x) := by
  have hd := (hf (a - x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_sub a)
  have he := congrArg (fun L : Space n →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hd.fderiv
  simpa [coordinateDerivative, Function.comp_def] using he

/-- The two signs cancel in every actual diagonal second derivative of a reflected test. -/
theorem coordinateHessian_const_sub {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    (a x : Space n) (i j : Fin n) :
    coordinateHessian (fun y => f (a - y)) x i j = coordinateHessian f (a - x) i j := by
  have hd : coordinateDerivative (fun y => f (a - y)) j =
      fun y => -coordinateDerivative f j (a - y) :=
    funext (fun y => coordinateDerivative_const_sub (hf.differentiable (by norm_num)) a y j)
  unfold coordinateHessian
  rw [hd]
  have hneg (F : Space n → ℝ) : coordinateDerivative (fun y => -F y) i x =
      -coordinateDerivative F i x := by simp [coordinateDerivative, fderiv_fun_neg]
  rw [hneg, coordinateDerivative_const_sub
    ((contDiff_coordinateDerivative hf (m := 1) (by norm_num) j).differentiable (by norm_num))]
  simp

end KLS
end

#print axioms KLS.mollify_contDiff
#print axioms KLS.mollify_tendsto_ae
#print axioms KLS.eLpNorm_mollify_le
#print axioms KLS.coordinateDerivative_scalarConvolution
#print axioms KLS.coordinateHessian_const_sub
