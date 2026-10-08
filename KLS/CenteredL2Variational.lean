import KLS.BrascampLiebDuality

/-!
# Centered L² variational bounds with a visible closure premise

The Hilbert-space quadratic objective is continuous. A bound on an actual
subset therefore passes to its norm closure. For probability measures,
centering in L² has squared norm equal to the actual real variance. These
lemmas prove the limit passage; they do not assert density of any operator range.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Filter Set
open scoped Topology ENNReal

noncomputable section
namespace KLS.CenteredL2

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

def oneLp : Lp ℝ 2 μ :=
  (memLp_const (μ := μ) (p := (2 : ℝ≥0∞)) (1 : ℝ)).toLp (fun _ : Ω => (1 : ℝ))

lemma oneLp_ae : (oneLp μ : Ω → ℝ) =ᵐ[μ] fun _ => 1 :=
  (memLp_const (μ := μ) (p := (2 : ℝ≥0∞)) (1 : ℝ)).coeFn_toLp

lemma integral_oneLp : (∫ x, oneLp μ x ∂μ) = 1 := by
  rw [integral_congr_ae (oneLp_ae μ)]
  simp

lemma inner_oneLp (u : Lp ℝ 2 μ) : inner ℝ (oneLp μ) u = ∫ x, u x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [oneLp_ae μ] with x hx
  simp [hx, RCLike.inner_apply]

/-- Subtract the actual mean in the genuine L² space. -/
def center (u : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  u - (∫ x, u x ∂μ) • oneLp μ

lemma center_ae (u : Lp ℝ 2 μ) :
    (center μ u : Ω → ℝ) =ᵐ[μ] fun x => u x - ∫ y, u y ∂μ := by
  filter_upwards [Lp.coeFn_sub u ((∫ x, u x ∂μ) • oneLp μ),
    Lp.coeFn_smul (∫ x, u x ∂μ) (oneLp μ), oneLp_ae μ] with x hx hy hz
  change (u - (∫ y, u y ∂μ) • oneLp μ) x = _
  rw [hx, Pi.sub_apply, hy, Pi.smul_apply, smul_eq_mul, hz, mul_one]

lemma integral_center (u : Lp ℝ 2 μ) : (∫ x, center μ u x ∂μ) = 0 := by
  rw [integral_congr_ae (center_ae μ u),
    integral_sub ((Lp.memLp u).integrable (by norm_num)) (integrable_const _)]
  simp

lemma inner_sub_center_center (u : Lp ℝ 2 μ) :
    inner ℝ (u - center μ u) (center μ u) = 0 := by
  have heq : u - center μ u = (∫ x, u x ∂μ) • oneLp μ := by
    rw [center]
    abel
  rw [heq, inner_smul_left, inner_oneLp, integral_center]
  simp

/-- Squared centered L² norm is the actual variance, with L² membership already supplied. -/
lemma norm_center_sq_eq_variance (u : Lp ℝ 2 μ) :
    ‖center μ u‖ ^ 2 = ProbabilityTheory.variance (fun x => u x) μ := by
  rw [ProbabilityTheory.variance_eq_integral (Lp.memLp u).aemeasurable,
    ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [center_ae μ u] with x hx
  simp [hx, RCLike.inner_apply, pow_two]

/-- A continuous quadratic objective carries a bound from a set to its closure. -/
theorem norm_sq_le_of_mem_closure_dual {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {S : Set H} {u f : H} {C : ℝ}
    (hu : u ∈ closure S) (horth : inner ℝ (f - u) u = 0)
    (hbound : ∀ v ∈ S, 2 * inner ℝ f v - ‖v‖ ^ 2 ≤ C) : ‖u‖ ^ 2 ≤ C := by
  have hclosed : IsClosed {v : H | 2 * inner ℝ f v - ‖v‖ ^ 2 ≤ C} :=
    isClosed_le (by fun_prop) continuous_const
  have hlimit := (closure_minimal hbound hclosed) hu
  change 2 * inner ℝ f u - ‖u‖ ^ 2 ≤ C at hlimit
  have hinner : inner ℝ f u = ‖u‖ ^ 2 := by
    calc
      inner ℝ f u = inner ℝ (u + (f - u)) u := by congr 1; abel
      _ = _ := by rw [inner_add_left, real_inner_self_eq_norm_sq, horth, add_zero]
  rw [hinner] at hlimit
  linarith

/-- The centered variational bridge. The norm-closure membership remains an explicit hypothesis. -/
theorem variance_le_of_center_mem_closure {S : Set (Lp ℝ 2 μ)} {u : Lp ℝ 2 μ} {C : ℝ}
    (hu : center μ u ∈ closure S)
    (hbound : ∀ v ∈ S, 2 * inner ℝ u v - ‖v‖ ^ 2 ≤ C) :
    ProbabilityTheory.variance (fun x => u x) μ ≤ C := by
  rw [← norm_center_sq_eq_variance]
  exact norm_sq_le_of_mem_closure_dual hu (inner_sub_center_center μ u) hbound

end KLS.CenteredL2
end

#print axioms KLS.CenteredL2.center_ae
#print axioms KLS.CenteredL2.integral_center
#print axioms KLS.CenteredL2.norm_center_sq_eq_variance
#print axioms KLS.CenteredL2.norm_sq_le_of_mem_closure_dual
#print axioms KLS.CenteredL2.variance_le_of_center_mem_closure
