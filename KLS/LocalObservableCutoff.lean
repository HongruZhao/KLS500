import KLS.LocalObservableGenerator
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! A compactly supported smooth observable agreeing through a whole state ball. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
noncomputable section
namespace KLS.LocalDiffusion
variable {N : ℕ}

def observableBump (R : ℝ) : ContDiffBump (0 : Fin N → ℝ) where
  rIn := |R| + 1
  rOut := |R| + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

def cutoffObservable (f : (Fin N → ℝ) → ℝ) (R : ℝ) : (Fin N → ℝ) → ℝ :=
  fun z => observableBump R z * f z

theorem contDiff_cutoffObservable {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffObservable f R) :=
  (observableBump R).contDiff.mul hf

theorem hasCompactSupport_cutoffObservable (f : (Fin N → ℝ) → ℝ) (R : ℝ) :
    HasCompactSupport (cutoffObservable f R) :=
  (observableBump R).hasCompactSupport.mul_right

theorem cutoffObservable_eventuallyEq (f : (Fin N → ℝ) → ℝ) (R : ℝ)
    {z : Fin N → ℝ} (hz : ‖z‖ ≤ R) : cutoffObservable f R =ᶠ[𝓝 z] f := by
  have hz' : z ∈ Metric.ball 0 (observableBump (N := N) R).rIn := by
    simp only [Metric.mem_ball, dist_zero_right, observableBump]
    exact lt_of_le_of_lt (hz.trans (le_abs_self R)) (by linarith)
  filter_upwards [(observableBump (N := N) R).eventuallyEq_one_of_mem_ball hz'] with x hx
  simp [cutoffObservable, hx]

theorem cutoffObservable_eq (f : (Fin N → ℝ) → ℝ) (R : ℝ)
    {z : Fin N → ℝ} (hz : ‖z‖ ≤ R) : cutoffObservable f R z = f z :=
  (cutoffObservable_eventuallyEq f R hz).eq_of_nhds

theorem fderiv_cutoffObservable_eq (f : (Fin N → ℝ) → ℝ) (R : ℝ)
    {z : Fin N → ℝ} (hz : ‖z‖ ≤ R) : fderiv ℝ (cutoffObservable f R) z = fderiv ℝ f z :=
  (cutoffObservable_eventuallyEq f R hz).fderiv_eq

theorem fderiv_fderiv_cutoffObservable_eq (f : (Fin N → ℝ) → ℝ) (R : ℝ)
    {z : Fin N → ℝ} (hz : ‖z‖ ≤ R) :
    fderiv ℝ (fderiv ℝ (cutoffObservable f R)) z = fderiv ℝ (fderiv ℝ f) z :=
  (cutoffObservable_eventuallyEq f R hz).fderiv.fderiv_eq

theorem exists_bound_fderiv_cutoffObservable {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z, ‖fderiv ℝ (cutoffObservable f R) z‖ ≤ K := by
  obtain ⟨C, hC⟩ := ((hasCompactSupport_cutoffObservable f R).fderiv ℝ).exists_bound_of_continuous
    ((contDiff_cutoffObservable hf R).continuous_fderiv (by simp))
  exact ⟨max C 0, le_max_right _ _, fun z => (hC z).trans (le_max_left _ _)⟩

end KLS.LocalDiffusion
end
#print axioms KLS.LocalDiffusion.exists_bound_fderiv_cutoffObservable
