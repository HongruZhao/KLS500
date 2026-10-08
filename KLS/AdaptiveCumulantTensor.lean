import KLS.TensorWhitenedGenerator

/-! Actual full coordinate arrays for a fixed directional cumulant slice,
and their already-proved localization drift and noise. -/
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
variable {n r : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def cumulantSliceDirections (u : Space n) (a : Fin r → Fin n) : Fin (r+1) → Space n :=
  Fin.cons u (fun s => EuclideanSpace.single (a s) 1)

def coordinateCumulantTensor (μ : Measure (Space n)) (r : ℕ) (u : Space n)
    (z : Fin (n+n*n) → ℝ) : (Fin r → Fin n) → ℝ :=
  fun a => coordinateCumulant μ (r+1) (cumulantSliceDirections u a) z

def lowerCumulantTensor (μ : Measure (Space n)) (r : ℕ) (u : Space n)
    (z : Fin (n+n*n) → ℝ) : (Fin r → Fin n) → ℝ :=
  fun a => lowerCumulantDrift μ (cumulantSliceDirections u a) z 0

def nextCumulantTensor (μ : Measure (Space n)) (r : ℕ) (u : Space n)
    (k : Fin n) (z : Fin (n+n*n) → ℝ) : (Fin r → Fin n) → ℝ :=
  fun a => cumulantNoiseCoefficient μ (r+1) (cumulantSliceDirections u a) k z

theorem contDiff_coordinateCumulantTensor (hμ : IsCompact μ.support) (u : Space n) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateCumulantTensor μ r u) := by
  apply contDiff_pi.mpr
  intro a
  exact contDiff_coordinateCumulant hμ (Nat.succ_ne_zero r) (cumulantSliceDirections u a)

theorem fderiv_coordinateCumulantTensor_diffusion (hμ : IsCompact μ.support)
    (u : Space n) (z : Fin (n+n*n) → ℝ) (k : Fin n) :
    fderiv ℝ (coordinateCumulantTensor μ r u) z (coordinateDiffusion μ k z) =
      nextCumulantTensor μ r u k z := by
  funext a
  rw [← fderiv_vector_entry ((contDiff_coordinateCumulantTensor hμ u).differentiable (by simp) z) a]
  exact coordinateCumulantGradient_diffusion hμ (Nat.succ_ne_zero r)
    (cumulantSliceDirections u a) z k

theorem differentialGenerator_coordinateCumulant (hμ : IsCompact μ.support)
    {m : ℕ} (hm : m ≠ 0) (h : Fin m → Space n) (z : Fin (n+n*n) → ℝ) :
    differentialGenerator (coordinateDrift μ z) (fun k => coordinateDiffusion μ k z)
      (coordinateCumulant μ m h) z = cumulantGenerator μ m h z := by
  unfold differentialGenerator cumulantGenerator coordinateCumulantGradient coordinateCumulantHessian
  simp only [smul_eq_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro k _
  change fderiv ℝ (fun y => coordinateCumulantGradient μ m h y (coordinateDiffusion μ k z)) z
    (coordinateDiffusion μ k z) = _
  rw [fderiv_clm_apply ((contDiff_coordinateCumulantGradient m h hμ hm).differentiable (by simp) z)
    (differentiableAt_const (coordinateDiffusion μ k z))]
  simp

/-- Both drift terms are actual coordinate cumulants of the current law. -/
theorem coordinateCumulantTensor_generator (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 2 ≤ r)
    (u : Space n) (z : Fin (n+n*n) → ℝ) :
    differentialGenerator (coordinateDrift μ z) (fun k => coordinateDiffusion μ k z)
      (coordinateCumulantTensor μ r u) z =
      -(((r+1 : ℕ) : ℝ) • coordinateCumulantTensor μ r u z + lowerCumulantTensor μ r u z) := by
  funext a
  have he := differentialGenerator_compCLM (ContinuousLinearMap.proj a)
    (contDiff_coordinateCumulantTensor hμ u) (coordinateDrift μ z)
    (fun k => coordinateDiffusion μ k z) z
  change differentialGenerator (coordinateDrift μ z) (fun k => coordinateDiffusion μ k z)
    (coordinateCumulant μ (r+1) (cumulantSliceDirections u a)) z =
    differentialGenerator (coordinateDrift μ z) (fun k => coordinateDiffusion μ k z)
      (coordinateCumulantTensor μ r u) z a at he
  rw [← he, differentialGenerator_coordinateCumulant hμ (Nat.succ_ne_zero r)]
  exact cumulantGenerator_eq_neg_order_add_lower hμ hfull (by omega)
    (cumulantSliceDirections u a) z 0

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.coordinateCumulantTensor_generator
#print axioms KLS.AdaptiveLocalization.fderiv_coordinateCumulantTensor_diffusion
