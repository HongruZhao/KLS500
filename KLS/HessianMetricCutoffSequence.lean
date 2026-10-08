import KLS.HessianMetricCutoffBound
import KLS.SmoothCutoffSequence

/-!
# A concrete monotone sublevel-cutoff sequence with vanishing diffusion error

The scale is `1/(k+1)`. Coercivity, the minimizer and the scale-independent
error constant are derived from the stated potential assumptions.
-/

open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

def hessianMetricCutoffSequence (φ : Space n → ℝ) (x₀ : Space n) (k : ℕ) : Space n → ℝ :=
  potentialSublevelCutoff φ x₀ (cutoffScale k)

lemma cutoffScale_antitone : Antitone cutoffScale := by
  intro i j hij
  unfold cutoffScale
  apply inv_anti₀ (by positivity)
  exact_mod_cast Nat.add_le_add_right hij 1

lemma hessianMetricCutoffSequence_monotone {φ : Space n → ℝ} {x₀ : Space n}
    (hmin : ∀ x, φ x₀ ≤ φ x) (x : Space n) :
    Monotone (fun k => hessianMetricCutoffSequence φ x₀ k x) := by
  intro i j hij
  apply sublevelCutoffProfile_antitone
  exact mul_le_mul_of_nonneg_right (cutoffScale_antitone hij)
    (zero_le_one.trans (potentialHeight_ge_one hmin x))

lemma hessianMetricCutoffSequence_tendsto_one (φ : Space n → ℝ) (x₀ x : Space n) :
    Tendsto (fun k => hessianMetricCutoffSequence φ x₀ k x) atTop (𝓝 1) :=
  (potentialSublevelCutoff_tendsto_one φ x₀ x).comp cutoffScale_tendsto_zero

/-- Actual A.4-type cutoffs, with C² regularity sufficient for all proved
integration identities. No cutoff, coercivity or error estimate is assumed. -/
theorem exists_hessianMetricCutoffSequence {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hconv : ConvexOn ℝ univ φ) [IsProbabilityMeasure (potentialMeasure φ)]
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (hgrad : Bornology.IsBounded (range (gradient φ))) :
    ∃ x₀ : Space n, (∀ x, φ x₀ ≤ φ x) ∧
      (∀ k, ContDiff ℝ 2 (hessianMetricCutoffSequence φ x₀ k) ∧
        HasCompactSupport (hessianMetricCutoffSequence φ x₀ k) ∧
        ∀ x, hessianMetricCutoffSequence φ x₀ k x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, Monotone (fun k => hessianMetricCutoffSequence φ x₀ k x)) ∧
      (∀ x, Tendsto (fun k => hessianMetricCutoffSequence φ x₀ k x) atTop (𝓝 1)) ∧
      (∀ k, Integrable (hessianMetricDiffusion φ V (hessianMetricCutoffSequence φ x₀ k))
        (potentialMeasure φ)) ∧
      Tendsto (fun k => ∫ x, ‖hessianMetricDiffusion φ V (hessianMetricCutoffSequence φ x₀ k) x‖
        ∂potentialMeasure φ) atTop (𝓝 0) := by
  obtain ⟨x₀, hmin, K, hK, hbound⟩ := exists_potentialSublevelCutoff_L1_bound hφ hV hconv hpos hMA hgrad
  refine ⟨x₀, hmin, ?_, hessianMetricCutoffSequence_monotone hmin,
    hessianMetricCutoffSequence_tendsto_one φ x₀, ?_, ?_⟩
  · intro k
    exact ⟨potentialSublevelCutoff_contDiff hφ x₀ (cutoffScale k),
      potentialSublevelCutoff_hasCompactSupport hφ.continuous hconv x₀ (cutoffScale_pos k),
      fun x => potentialSublevelCutoff_mem_Icc φ x₀ x (cutoffScale k)⟩
  · intro k
    exact (hbound (cutoffScale k) (cutoffScale_pos k)).1
  · apply squeeze_zero (fun k => integral_nonneg (fun x => norm_nonneg _))
      (fun k => (hbound (cutoffScale k) (cutoffScale_pos k)).2)
    simpa using cutoffScale_tendsto_zero.mul_const K

end KLS
end

#print axioms KLS.hessianMetricCutoffSequence_monotone
#print axioms KLS.hessianMetricCutoffSequence_tendsto_one
#print axioms KLS.exists_hessianMetricCutoffSequence
