import KLS.AdaptiveDiffusionRegularity
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-! Finite coordinate state for the actual adaptive parameter and its coefficients. -/
open MeasureTheory ProbabilityTheory Set Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS.AdaptiveLocalization
variable {n : ℕ}

def encodeState (p : Parameter n) : Fin (n + n * n) → ℝ :=
  Fin.addCases p.1 (fun a => p.2 (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2)

def decodeState (z : Fin (n + n * n) → ℝ) : Parameter n :=
  ((fun i => z (Fin.castAdd (n * n) i)),
    fun i j => z (Fin.natAdd n (finProdFinEquiv (i,j))))

@[simp] theorem decode_encodeState (p : Parameter n) : decodeState (encodeState p) = p := by
  apply Prod.ext
  · funext i
    simp only [decodeState, encodeState, Fin.addCases_left]
  · funext i j
    simp only [decodeState, encodeState, Fin.addCases_right, Equiv.symm_apply_apply]

@[simp] theorem encode_decodeState (z : Fin (n + n * n) → ℝ) : encodeState (decodeState z) = z := by
  funext a
  refine Fin.addCases ?_ ?_ a
  · intro i
    simp only [decodeState, encodeState, Fin.addCases_left]
  · intro ij
    simp only [decodeState, encodeState, Fin.addCases_right, Prod.mk.eta, Equiv.apply_symm_apply]

@[simp] theorem encodeState_zero : encodeState (0 : Parameter n) = 0 := by
  funext a
  refine Fin.addCases ?_ ?_ a <;> simp [encodeState]

@[simp] theorem decodeState_zero : decodeState (0 : Fin (n + n * n) → ℝ) = 0 := by
  ext <;> rfl

theorem contDiff_encodeState : ContDiff ℝ (⊤ : ℕ∞) (encodeState (n := n)) := by
  apply contDiff_pi.mpr
  intro a
  refine Fin.addCases ?_ ?_ a
  · intro i
    simp only [encodeState, Fin.addCases_left]
    fun_prop
  · intro ij
    simp only [encodeState, Fin.addCases_right]
    fun_prop

theorem contDiff_decodeState : ContDiff ℝ (⊤ : ℕ∞) (decodeState (n := n)) := by
  unfold decodeState
  fun_prop

def coordinateDrift (μ : Measure (Space n)) (z : Fin (n + n * n) → ℝ) :
    Fin (n + n * n) → ℝ := encodeState (drift μ (decodeState z))

def coordinateDiffusion (μ : Measure (Space n)) (k : Fin n)
    (z : Fin (n + n * n) → ℝ) : Fin (n + n * n) → ℝ :=
  encodeState (diffusion μ k (decodeState z))

variable {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem locallyLipschitz_coordinateDrift (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) : LocallyLipschitz (coordinateDrift μ) :=
  ((contDiff_encodeState.of_le (by simp)).locallyLipschitz).comp
    ((locallyLipschitz_drift hμ hfull).comp
      ((contDiff_decodeState.of_le (by simp)).locallyLipschitz))

theorem locallyLipschitz_coordinateDiffusion (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (k : Fin n) :
    LocallyLipschitz (coordinateDiffusion μ k) :=
  ((contDiff_encodeState.of_le (by simp)).locallyLipschitz).comp
    ((locallyLipschitz_diffusion hμ hfull k).comp
      ((contDiff_decodeState.of_le (by simp)).locallyLipschitz))

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.locallyLipschitz_coordinateDrift
#print axioms KLS.AdaptiveLocalization.locallyLipschitz_coordinateDiffusion
