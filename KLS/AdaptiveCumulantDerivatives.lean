import KLS.TiltCumulantHierarchy
import KLS.AdaptiveLogPartition
import KLS.DirectionalWordAffine

/-! Actual cumulants as smooth state observables and their genuine adaptive noise. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.StandardLocalization
variable {n m : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def coordinateCumulant (μ : Measure (Space n)) (m : ℕ) (h : Fin m → Space n)
    (z : Fin (n+n*n) → ℝ) : ℝ := cumulantTensor (law μ (decodeState z).1 (decodeState z).2) m h

/-- Every nonzero-order cumulant is the actual state log-partition derivative. -/
theorem coordinateCumulant_eq_word (hμ : IsCompact μ.support) (hm : m ≠ 0)
    (h : Fin m → Space n) (z : Fin (n+n*n) → ℝ) :
    coordinateCumulant μ m h z =
      directionalWordDerivative (coordinateLogPartition μ) ((List.ofFn h).map linearStateCLM) z := by
  have he : tiltLogLaplace (law μ (decodeState z).1 (decodeState z).2) =
      fun w => coordinateLogPartition μ (z+linearStateCLM w) - coordinateLogPartition μ z := by
    funext w
    exact coordinateLogMGF_eq_partition_difference hμ z w
  letI := law_isProbability hμ (decodeState z).1 (decodeState z).2
  have hc := contDiff_tiltLogLaplace (μ := law μ (decodeState z).1 (decodeState z).2)
    (by rwa [support_law hμ])
  change iteratedFDeriv ℝ m (tiltLogLaplace (law μ (decodeState z).1 (decodeState z).2)) 0 h = _
  rw [← directionalWordDerivative_ofFn hc, he]
  have hshift : ContDiff ℝ (⊤ : ℕ∞) (fun w : Space n => coordinateLogPartition μ (z+linearStateCLM w)) :=
    (contDiff_coordinateLogPartition hμ).comp (contDiff_const.add linearStateCLM.contDiff)
  rw [directionalWordDerivative_sub hshift (contDiff_const (c := coordinateLogPartition μ z))]
  have hne : List.ofFn h ≠ [] := by
    intro heq
    have hh := congrArg List.length heq
    apply hm
    simpa only [List.length_ofFn, List.length_nil] using hh
  rw [directionalWordDerivative_const_of_ne_nil _ _ hne]
  simp only [Pi.zero_apply, sub_zero]
  rw [directionalWordDerivative_comp_affine (contDiff_coordinateLogPartition hμ)]
  simp only [map_zero, add_zero]

theorem contDiff_coordinateCumulant (hμ : IsCompact μ.support) (hm : m ≠ 0)
    (h : Fin m → Space n) : ContDiff ℝ (⊤ : ℕ∞) (coordinateCumulant μ m h) := by
  have he : coordinateCumulant μ m h =
      directionalWordDerivative (coordinateLogPartition μ) ((List.ofFn h).map linearStateCLM) :=
    funext (coordinateCumulant_eq_word hμ hm h)
  rw [he]
  exact contDiff_directionalWordDerivative (contDiff_coordinateLogPartition hμ) _

def coordinateCumulantGradient (μ : Measure (Space n)) (m : ℕ) (h : Fin m → Space n) :=
  fderiv ℝ (coordinateCumulant μ m h)

def coordinateCumulantHessian (μ : Measure (Space n)) (m : ℕ) (h : Fin m → Space n)
    (z : Fin (n+n*n) → ℝ) : (Fin (n+n*n) → ℝ) →L[ℝ] (Fin (n+n*n) → ℝ) →L[ℝ] ℝ :=
  fderiv ℝ (coordinateCumulantGradient μ m h) z

theorem coordinateCumulantGradient_apply (hμ : IsCompact μ.support) (hm : m ≠ 0)
    (h : Fin m → Space n) (z v : Fin (n+n*n) → ℝ) :
    coordinateCumulantGradient μ m h z v =
      directionalWordDerivative (coordinateLogPartition μ)
        (v :: (List.ofFn h).map linearStateCLM) z := by
  have he := funext (coordinateCumulant_eq_word hμ hm h)
  simp only [coordinateCumulantGradient, he, directionalWordDerivative_cons]

theorem coordinateCumulantHessian_apply (hμ : IsCompact μ.support) (hm : m ≠ 0)
    (h : Fin m → Space n) (z u v : Fin (n+n*n) → ℝ) :
    coordinateCumulantHessian μ m h z u v =
      directionalWordDerivative (coordinateLogPartition μ)
        (u :: v :: (List.ofFn h).map linearStateCLM) z := by
  change fderiv ℝ (fderiv ℝ (coordinateCumulant μ m h)) z u v = _
  rw [fderiv_fderiv_apply_eq_word (contDiff_coordinateCumulant hμ hm h)]
  have he := funext (coordinateCumulant_eq_word hμ hm h)
  rw [he, directionalWordDerivative_append]
  rfl

/-- The martingale coefficient is the genuine next cumulant in the whitening direction. -/
theorem coordinateCumulantGradient_diffusion (hμ : IsCompact μ.support) (hm : m ≠ 0)
    (h : Fin m → Space n) (z : Fin (n+n*n) → ℝ) (k : Fin n) :
    coordinateCumulantGradient μ m h z (coordinateDiffusion μ k z) =
      cumulantTensor (law μ (decodeState z).1 (decodeState z).2) (m+1)
        (Fin.cons (inverseSqrtDirection μ z k) h) := by
  rw [coordinateCumulantGradient_apply hμ hm]
  change _ = coordinateCumulant μ (m+1) (Fin.cons (inverseSqrtDirection μ z k) h) z
  rw [coordinateCumulant_eq_word hμ (Nat.succ_ne_zero m)]
  simp only [List.ofFn_cons, List.map_cons, linearState_inverseSqrtDirection]

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.coordinateCumulantGradient_diffusion
#print axioms KLS.AdaptiveLocalization.coordinateCumulantHessian_apply
