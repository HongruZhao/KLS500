import KLS.Definitions
import Mathlib.Topology.Order.Compact

/-! Coercive sublevels eventually lie in any open neighborhood of the actual zero set. -/
open Set Metric
open scoped Topology
noncomputable section
namespace KLS
variable {n : ℕ}

theorem isCompact_sublevel_of_norm_lower {f : Space n → ℝ} {a A : ℝ}
    (hf : Continuous f) (ha : 0 < a) (hlower : ∀ x, a * ‖x‖ - A ≤ f x)
    (t : ℝ) : IsCompact {x | f x ≤ t} := by
  apply (isCompact_closedBall (0 : Space n) ((t + A) / a)).of_isClosed_subset
    (isClosed_le hf continuous_const)
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  apply (le_div_iff₀ ha).mpr
  have h := (hlower x).trans hx
  nlinarith

/-- Nonnegativity, continuity and an explicit radial lower bound provide an actual
positive compact sublevel inside any open set containing all zeros. -/
theorem exists_pos_compact_sublevel_subset {f : Space n → ℝ} {a A : ℝ}
    (hf : Continuous f) (hnon : ∀ x, 0 ≤ f x) (ha : 0 < a)
    (hlower : ∀ x, a * ‖x‖ - A ≤ f x) {U : Set (Space n)}
    (hU : IsOpen U) (hzeros : {x | f x = 0} ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ IsCompact {x | f x ≤ ε} ∧ {x | f x ≤ ε} ⊆ U := by
  let K : Set (Space n) := {x | f x ≤ 1} ∩ Uᶜ
  have hK : IsCompact K := (isCompact_sublevel_of_norm_lower hf ha hlower 1).inter_right
    hU.isClosed_compl
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hf.continuousOn
    have hpos : 0 < f x := by
      apply lt_of_le_of_ne (hnon x)
      intro heq
      exact hx.2 (hzeros heq.symm)
    refine ⟨min 1 (f x / 2), lt_min (by norm_num) (by positivity),
      isCompact_sublevel_of_norm_lower hf ha hlower _, ?_⟩
    intro y hy
    by_contra hyU
    have hyK : y ∈ K := ⟨(show f y ≤ min 1 (f x / 2) from hy).trans
      (min_le_left _ _), hyU⟩
    have hxy : f x ≤ f y := hmin hyK
    have hy' := (show f y ≤ min 1 (f x / 2) from hy).trans (min_le_right _ _)
    linarith
  · refine ⟨1, by norm_num, isCompact_sublevel_of_norm_lower hf ha hlower 1, ?_⟩
    intro x hx
    by_contra hxU
    exact hne ⟨x, hx, hxU⟩

end KLS
end
#print axioms KLS.isCompact_sublevel_of_norm_lower
#print axioms KLS.exists_pos_compact_sublevel_subset
