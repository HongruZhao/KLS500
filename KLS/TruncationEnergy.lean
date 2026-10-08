import KLS.Definitions
import KLS.LocalRademacher
import KLS.PairwiseL2

/-!
# Value truncation decreases Dirichlet energy

Absolute continuity is explicit in this module. No bridge from compact-set
log-concavity to absolute continuity is assumed. The resulting theorem transfers
an L² Poincaré inequality to its finite-energy formulation with the same constant;
it does not assert that any dimension-free Poincaré constant exists.
-/

open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal NNReal Topology

namespace KLS

/-- A one-Lipschitz scalar composition cannot increase the derivative norm where
the inner function is differentiable. This also covers the total derivative's
zero default if the composition is not differentiable at that point. -/
theorem norm_fderiv_comp_le_of_lipschitzOne
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {g : ℝ → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : LipschitzWith 1 g) :
    ‖fderiv ℝ (g ∘ f) x‖ ≤ ‖fderiv ℝ f x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  apply norm_fderiv_le_of_lip' ℝ (add_nonneg (norm_nonneg _) hε.le)
  filter_upwards [hf.hasFDerivAt.isLittleO.def hε] with y hy
  calc
    ‖(g ∘ f) y - (g ∘ f) x‖ ≤ ‖f y - f x‖ := by
      simpa only [Function.comp_apply, NNReal.coe_one, one_mul] using hg.norm_sub_le (f y) (f x)
    _ = ‖(f y - f x - fderiv ℝ f x (y - x)) + fderiv ℝ f x (y - x)‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖f y - f x - fderiv ℝ f x (y - x)‖ + ‖fderiv ℝ f x (y - x)‖ :=
      norm_add_le _ _
    _ ≤ ε * ‖y - x‖ + ‖fderiv ℝ f x‖ * ‖y - x‖ :=
      add_le_add hy ((fderiv ℝ f x).le_opNorm (y - x))
    _ = (‖fderiv ℝ f x‖ + ε) * ‖y - x‖ := by ring

/-- Symmetric clipping decreases the derivative norm at differentiability points
of the unclipped function. -/
theorem norm_fderiv_symmetricTruncation_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (m : ℕ) :
    ‖fderiv ℝ (symmetricTruncation m f) x‖ ≤ ‖fderiv ℝ f x‖ := by
  exact norm_fderiv_comp_le_of_lipschitzOne hf
    ((LipschitzWith.id.min_const (m : ℝ)).const_max (-(m : ℝ)))

/-- Value truncation decreases extended Dirichlet energy for a locally Lipschitz
function and a measure absolutely continuous with respect to volume. -/
theorem energy_symmetricTruncation_le {n : ℕ} {μ : Measure (Space n)}
    (hμ : μ ≪ (volume : Measure (Space n)))
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (m : ℕ) :
    energy μ (symmetricTruncation m f) ≤ energy μ f := by
  apply lintegral_mono_ae
  filter_upwards [locallyLipschitz_ae_differentiableAt_of_absolutelyContinuous hμ hf]
    with x hx
  apply ENNReal.ofReal_le_ofReal
  have hnorm : ‖gradient (symmetricTruncation m f) x‖ ≤ ‖gradient f x‖ := by
    rw [norm_gradient_eq_norm_fderiv, norm_gradient_eq_norm_fderiv]
    exact norm_fderiv_symmetricTruncation_le hx m
  gcongr

/-- The finite-energy endpoint follows from the L² test-function inequality at
the same finite nonnegative constant. The L² conclusion is proved by truncation
and Fatou, not assumed. -/
theorem finiteEnergy_poincare_of_mem_constants {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : μ ≪ (volume : Measure (Space n)))
    {C : ℝ≥0} (hC : C ∈ poincareConstants μ)
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (henergy : energy μ f < ∞) :
    MemLp f 2 μ ∧ variance μ f ≤ (C : ℝ≥0∞) * energy μ f := by
  have hfm : AEStronglyMeasurable f μ := hf.continuous.measurable.aestronglyMeasurable
  apply memLp_two_and_evariance_le_of_truncation_bound hfm
  · intro m
    have htrunc := hC (symmetricTruncation m f)
      ⟨locallyLipschitz_symmetricTruncation hf m, memLp_two_symmetricTruncation hfm m⟩
    exact htrunc.trans (mul_le_mul_right (energy_symmetricTruncation_le hμ hf m) C)
  · exact ENNReal.mul_lt_top ENNReal.coe_lt_top henergy

/-- For a positive finite constant, the L² convention and the finite-energy
convention agree under absolute continuity. Positivity is explicit because the
extended product `0 * ∞` is zero. -/
theorem mem_poincareConstants_iff_finiteEnergy {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : μ ≪ (volume : Measure (Space n)))
    {C : ℝ≥0} (hpos : 0 < C) :
    C ∈ poincareConstants μ ↔
      ∀ f : Space n → ℝ, LocallyLipschitz f → energy μ f < ∞ →
        MemLp f 2 μ ∧ variance μ f ≤ (C : ℝ≥0∞) * energy μ f := by
  constructor
  · intro hC f hf he
    exact finiteEnergy_poincare_of_mem_constants hμ hC hf he
  · intro h f hf
    by_cases he : energy μ f < ∞
    · exact (h f hf.1 he).2
    · have hinf : energy μ f = ∞ := top_le_iff.mp (not_lt.mp he)
      rw [hinf, ENNReal.mul_top (by exact_mod_cast ne_of_gt hpos)]
      exact le_top

end KLS

#print axioms KLS.norm_fderiv_comp_le_of_lipschitzOne
#print axioms KLS.norm_fderiv_symmetricTruncation_le
#print axioms KLS.energy_symmetricTruncation_le
#print axioms KLS.finiteEnergy_poincare_of_mem_constants
#print axioms KLS.mem_poincareConstants_iff_finiteEnergy
