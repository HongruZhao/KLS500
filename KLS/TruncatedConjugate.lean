import KLS.FiniteConjugateC1
import KLS.MomentExponentialTails
import Mathlib.Analysis.Convex.Extrema

/-!
# Globally finite truncations of the actual conjugate

Taking the supremum over a genuine source ball yields a globally convex
Lipschitz potential. It agrees with the actual conjugate whenever the inverse
contact lies in that ball. Centering at an interior source point produces a
nonnegative coercive function whose zeros are exactly that point's original
subgradients.
-/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

def truncatedLegendrePotential (u : Space n → ℝ) (M : ℝ) (p : Space n) : ℝ :=
  sSup ((fun x => inner ℝ p x - u x) '' closedBall 0 M)

theorem le_truncatedLegendrePotential {u : Space n → ℝ} (hu : Continuous u)
    (M : ℝ) (p : Space n) {x : Space n} (hx : ‖x‖ ≤ M) :
    inner ℝ p x - u x ≤ truncatedLegendrePotential u M p := by
  have hcont : Continuous (fun x => inner ℝ p x - u x) :=
    (continuous_const.inner continuous_id).sub hu
  apply le_csSup ((isCompact_closedBall (0 : Space n) M).image hcont).bddAbove
  exact ⟨x, by simpa only [mem_closedBall, dist_zero_right] using hx, rfl⟩

theorem exists_truncatedLegendrePotential_eq {u : Space n → ℝ} (hu : Continuous u)
    {M : ℝ} (hM : 0 ≤ M) (p : Space n) :
    ∃ x : Space n, ‖x‖ ≤ M ∧ truncatedLegendrePotential u M p = inner ℝ p x - u x := by
  have hne : (closedBall (0 : Space n) M).Nonempty := ⟨0, mem_closedBall_self hM⟩
  have hcont : Continuous (fun x => inner ℝ p x - u x) :=
    (continuous_const.inner continuous_id).sub hu
  obtain ⟨x, hx, hmax⟩ := (isCompact_closedBall (0 : Space n) M).exists_isMaxOn hne hcont.continuousOn
  have hlub : IsLUB ((fun y => inner ℝ p y - u y) '' closedBall 0 M) (inner ℝ p x - u x) := by
    refine ⟨?_, ?_⟩
    · rintro a ⟨y, hy, rfl⟩
      exact hmax hy
    · intro a ha
      exact ha ⟨x, hx, rfl⟩
  exact ⟨x, by simpa only [mem_closedBall, dist_zero_right] using hx,
    hlub.csSup_eq (hne.image _)⟩

theorem convexOn_truncatedLegendrePotential {u : Space n → ℝ} (hu : Continuous u)
    {M : ℝ} (hM : 0 ≤ M) : ConvexOn ℝ univ (truncatedLegendrePotential u M) := by
  refine ⟨convex_univ, ?_⟩
  intro p _ q _ a b ha hb hab
  obtain ⟨x, hx, hval⟩ := exists_truncatedLegendrePotential_eq hu hM (a • p + b • q)
  have hp := mul_le_mul_of_nonneg_left (le_truncatedLegendrePotential hu M p hx) ha
  have hq := mul_le_mul_of_nonneg_left (le_truncatedLegendrePotential hu M q hx) hb
  rw [hval, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  change a * inner ℝ p x + b * inner ℝ q x - u x ≤
    a * truncatedLegendrePotential u M p + b * truncatedLegendrePotential u M q
  nlinarith [congrArg (fun r : ℝ => r * u x) hab]

theorem truncatedLegendrePotential_sub_le {u : Space n → ℝ} (hu : Continuous u)
    {M : ℝ} (hM : 0 ≤ M) (p q : Space n) :
    truncatedLegendrePotential u M p - truncatedLegendrePotential u M q ≤ M * ‖p - q‖ := by
  obtain ⟨x, hx, hval⟩ := exists_truncatedLegendrePotential_eq hu hM p
  have hq := le_truncatedLegendrePotential hu M q hx
  have hip := (real_inner_le_norm (p - q) x).trans
    (mul_le_mul_of_nonneg_left hx (norm_nonneg (p - q)))
  rw [inner_sub_left] at hip
  rw [hval]
  nlinarith

theorem lipschitzWith_truncatedLegendrePotential {u : Space n → ℝ} (hu : Continuous u)
    {M : ℝ} (hM : 0 ≤ M) : LipschitzWith ⟨M, hM⟩ (truncatedLegendrePotential u M) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [Real.dist_eq, dist_eq_norm]
  change |truncatedLegendrePotential u M p - truncatedLegendrePotential u M q| ≤ M * ‖p - q‖
  apply abs_le.mpr
  constructor
  · have hh := truncatedLegendrePotential_sub_le hu hM q p
    rw [norm_sub_rev] at hh
    linarith
  · exact truncatedLegendrePotential_sub_le hu hM p q

theorem truncatedLegendrePotential_le_finiteLegendrePotential
    {u : Space n → ℝ} {M : ℝ} (hM : 0 ≤ M)
    {p : Space n} (hp : p ∈ momentLegendreDomain u) :
    truncatedLegendrePotential u M p ≤ finiteLegendrePotential u p := by
  apply csSup_le ((show (closedBall (0 : Space n) M).Nonempty from
    ⟨0, mem_closedBall_self hM⟩).image _)
  rintro a ⟨x, hx, rfl⟩
  have hh := finiteLegendrePotential_young u hp x
  linarith

theorem truncatedLegendrePotential_eq_finiteLegendrePotential_of_contact
    {u : Space n → ℝ} (hu : Continuous u) {M : ℝ} (hM : 0 ≤ M)
    {p x : Space n} (hp : p ∈ convexSubgradient u x) (hx : ‖x‖ ≤ M) :
    truncatedLegendrePotential u M p = finiteLegendrePotential u p := by
  apply le_antisymm
  · exact truncatedLegendrePotential_le_finiteLegendrePotential hM
      (mem_momentLegendreDomain_of_support_any_normalization hp)
  · rw [finiteLegendrePotential_eq_of_mem_convexSubgradient hp]
    exact le_truncatedLegendrePotential hu M p hx

/-- A source point strictly inside the truncation ball has exactly the same
support contacts for the truncated and original convex problems. -/
theorem truncatedLegendrePotential_contact_iff
    {u : Space n → ℝ} (hu : Continuous u) (hc : ConvexOn ℝ univ u)
    {M : ℝ} {x p : Space n} (hx : ‖x‖ < M) :
    truncatedLegendrePotential u M p = inner ℝ p x - u x ↔ p ∈ convexSubgradient u x := by
  constructor
  · intro heq
    have hmin : IsMinOn (tiltedPotential u p) (closedBall 0 M) x := by
      intro y hy
      have hyM : ‖y‖ ≤ M := by simpa only [mem_closedBall, dist_zero_right] using hy
      have hh := le_truncatedLegendrePotential hu M p hyM
      rw [heq] at hh
      dsimp [tiltedPotential]
      linarith
    have hxnhds : closedBall (0 : Space n) M ∈ 𝓝 x := by
      have hxball : x ∈ ball (0 : Space n) M := by
        simpa only [mem_ball, dist_zero_right] using hx
      exact mem_of_superset (isOpen_ball.mem_nhds hxball) ball_subset_closedBall
    have hglobal := IsMinOn.of_isLocalMin_of_convex_univ (hmin.isLocalMin hxnhds)
      (convexOn_tiltedPotential hc p)
    intro y
    have hh := hglobal y
    dsimp [tiltedPotential] at hh
    rw [inner_sub_right]
    linarith
  · intro hp
    rw [truncatedLegendrePotential_eq_finiteLegendrePotential_of_contact hu
      (norm_nonneg x |>.trans hx.le) hp hx.le,
      finiteLegendrePotential_eq_of_mem_convexSubgradient hp]

def centeredTruncatedConjugate (u : Space n → ℝ) (x : Space n) (M : ℝ) (p : Space n) : ℝ :=
  truncatedLegendrePotential u M p - inner ℝ x p + u x

theorem centeredTruncatedConjugate_nonneg
    {u : Space n → ℝ} (hu : Continuous u) {x : Space n} {M : ℝ} (hx : ‖x‖ ≤ M)
    (p : Space n) : 0 ≤ centeredTruncatedConjugate u x M p := by
  have hh := le_truncatedLegendrePotential hu M p hx
  rw [real_inner_comm x p] at hh
  dsimp [centeredTruncatedConjugate]
  linarith

theorem centeredTruncatedConjugate_eq_zero_iff
    {u : Space n → ℝ} (hu : Continuous u) (hc : ConvexOn ℝ univ u)
    {x p : Space n} {M : ℝ} (hx : ‖x‖ < M) :
    centeredTruncatedConjugate u x M p = 0 ↔ p ∈ convexSubgradient u x := by
  rw [← truncatedLegendrePotential_contact_iff hu hc hx]
  dsimp [centeredTruncatedConjugate]
  rw [real_inner_comm p x]
  constructor <;> intro hh <;> linarith

end KLS
end

#print axioms KLS.convexOn_truncatedLegendrePotential
#print axioms KLS.lipschitzWith_truncatedLegendrePotential
#print axioms KLS.truncatedLegendrePotential_eq_finiteLegendrePotential_of_contact
#print axioms KLS.centeredTruncatedConjugate_eq_zero_iff
