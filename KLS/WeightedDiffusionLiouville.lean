import KLS.WeightedDiffusionRange

/-!
# The exact weak Liouville obligation behind diffusion-range density

Range density is equivalent to the assertion that a weighted L² function
annihilating every actual compact C³ diffusion test is almost everywhere
constant. This file proves the Hilbert-space equivalence, not the analytic
Liouville assertion itself.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter
open scoped Topology ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

/-- Precise analytic obligation: weak harmonic L² functions for the actual diffusion are constant. -/
def WeakDiffusionLiouville (φ : Space n → ℝ) : Prop :=
  ∀ u : Lp ℝ 2 (potentialMeasure φ),
    (∀ g : Space n → ℝ, ContDiff ℝ 3 g → HasCompactSupport g →
      (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) = 0) →
    ∃ c : ℝ, (u : Space n → ℝ) =ᵐ[potentialMeasure φ] fun _ => c

lemma inner_eq_neg_integral_diffusion_of_ae {φ g : Space n → ℝ}
    (u v : Lp ℝ 2 (potentialMeasure φ))
    (hv : (v : Space n → ℝ) =ᵐ[potentialMeasure φ] fun x => -weightedDiffusion φ g x) :
    inner ℝ u v = -(∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) := by
  rw [L2.inner_def, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hv] with x hx
  simp [hx, RCLike.inner_apply, mul_comm]

/-- Orthogonality to the actual L² range is exactly annihilation of actual diffusion tests. -/
theorem mem_orthogonal_compactDiffusionRange_iff {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (u : Lp ℝ 2 (potentialMeasure φ)) :
    u ∈ (compactDiffusionRange φ)ᗮ ↔
      ∀ g : Space n → ℝ, ContDiff ℝ 3 g → HasCompactSupport g →
        (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) = 0 := by
  rw [(compactDiffusionRange φ).mem_orthogonal']
  constructor
  · intro hu g hg hc
    let hv2 := (memLp_weightedDiffusion_of_hasCompactSupport hφ hg hc).neg
    let v : Lp ℝ 2 (potentialMeasure φ) := hv2.toLp (fun x => -weightedDiffusion φ g x)
    have hvae : (v : Space n → ℝ) =ᵐ[potentialMeasure φ] fun x => -weightedDiffusion φ g x :=
      hv2.coeFn_toLp
    have hv : v ∈ compactDiffusionRange φ := ⟨g, hg, hc, hvae⟩
    have he := hu v hv
    rw [inner_eq_neg_integral_diffusion_of_ae u v hvae] at he
    exact neg_eq_zero.mp he
  · intro hu v hv
    rcases hv with ⟨g, hg, hc, hv⟩
    rw [inner_eq_neg_integral_diffusion_of_ae u v hv, hu g hg hc, neg_zero]

/-- The analytic weak Liouville assertion suffices for genuine L² range density. -/
theorem diffusionRangeDense_of_weakDiffusionLiouville {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hweak : WeakDiffusionLiouville φ) :
    DiffusionRangeDense φ := by
  intro u hu
  rw [← (compactDiffusionRange φ).orthogonal_orthogonal_eq_closure]
  rw [((compactDiffusionRange φ)ᗮ).mem_orthogonal]
  intro v hv
  obtain ⟨c, hc⟩ := hweak v ((mem_orthogonal_compactDiffusionRange_iff hφ v).mp hv)
  rw [L2.inner_def]
  calc
    (∫ x, inner ℝ (v x) (u x) ∂potentialMeasure φ) =
        ∫ x, c * u x ∂potentialMeasure φ := by
      apply integral_congr_ae
      filter_upwards [hc] with x hx
      simp [hx, RCLike.inner_apply, mul_comm]
    _ = 0 := by rw [integral_const_mul, hu, mul_zero]

/-- Conversely, density forces every weak L² harmonic function to be constant. -/
theorem weakDiffusionLiouville_of_diffusionRangeDense {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hdense : DiffusionRangeDense φ) :
    WeakDiffusionLiouville φ := by
  intro u hu
  have ho : u ∈ (compactDiffusionRange φ)ᗮ :=
    (mem_orthogonal_compactDiffusionRange_iff hφ u).mpr hu
  have hoc : u ∈ (compactDiffusionRange φ).topologicalClosureᗮ := by
    rwa [Submodule.orthogonal_closure]
  have hc := hdense (CenteredL2.center (potentialMeasure φ) u)
    (CenteredL2.integral_center _ u)
  have hz : inner ℝ u (CenteredL2.center (potentialMeasure φ) u) = 0 :=
    ((compactDiffusionRange φ).topologicalClosure.mem_orthogonal' u).mp hoc _ hc
  have horth := CenteredL2.inner_sub_center_center (potentialMeasure φ) u
  rw [inner_sub_left, hz, zero_sub, neg_eq_zero] at horth
  have hcenter : CenteredL2.center (potentialMeasure φ) u = 0 :=
    inner_self_eq_zero.mp horth
  refine ⟨∫ x, u x ∂potentialMeasure φ, ?_⟩
  have hae := CenteredL2.center_ae (potentialMeasure φ) u
  rw [hcenter] at hae
  filter_upwards [hae, Lp.coeFn_zero ℝ 2 (potentialMeasure φ)] with x hx hy
  change (0 : Lp ℝ 2 (potentialMeasure φ)) x = u x - _ at hx
  rw [hy] at hx
  exact (sub_eq_zero.mp hx.symm)

/-- This equivalence isolates the remaining analytic obligation; it proves neither side. -/
theorem diffusionRangeDense_iff_weakDiffusionLiouville {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 2 φ) :
    DiffusionRangeDense φ ↔ WeakDiffusionLiouville φ :=
  ⟨weakDiffusionLiouville_of_diffusionRangeDense hφ,
    diffusionRangeDense_of_weakDiffusionLiouville hφ⟩

end KLS
end

#print axioms KLS.mem_orthogonal_compactDiffusionRange_iff
#print axioms KLS.diffusionRangeDense_of_weakDiffusionLiouville
#print axioms KLS.weakDiffusionLiouville_of_diffusionRangeDense
#print axioms KLS.diffusionRangeDense_iff_weakDiffusionLiouville
