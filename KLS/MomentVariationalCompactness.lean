import KLS.MomentExponentialTails

/-!
# Compact energy sublevels and the genuine moment-measure functional

The partition function is continuous along bounded-energy sequences because
isotropy yields one common integrable exponential bound. The energy is the
actual extended Legendre integral from `MomentLegendreEnergy`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

noncomputable section
namespace KLS

/-- The moment-measure variational functional. Its theorems below explicitly
require finite dual energy and prove finite positive partition function before
using the real logarithm or the energy's real value. -/
def momentVariationalFunctional {n : ℕ} (μ : Measure (Space n)) (φ : Space n → ℝ) : ℝ :=
  Real.log (momentPartitionFunction φ) - (momentDualEnergy μ φ).toReal

theorem isClosed_momentDualEnergy_sublevel {n : ℕ} (μ : Measure (Space n)) (M : ℝ≥0∞) :
    IsClosed {φ : C(Space n, ℝ) | momentDualEnergy μ φ ≤ M} := by
  apply IsSeqClosed.isClosed
  intro φ ψ hφ hlim
  have hp (x : Space n) : Tendsto (fun k => φ k x) atTop (𝓝 (ψ x)) :=
    (continuous_eval_const x).continuousAt.tendsto.comp hlim
  have hfatou := momentDualEnergy_le_liminf μ hp
  have hbound : liminf (fun k => momentDualEnergy μ (φ k)) atTop ≤ M := by
    calc
      _ ≤ liminf (fun _ : ℕ => M) atTop :=
        liminf_le_liminf (Eventually.of_forall hφ)
      _ = M := liminf_const M
  exact hfatou.trans hbound

/-- An actual compact subset of continuous convex potentials, with the given
finite or infinite energy threshold. -/
def normalizedMomentEnergySublevel (n : ℕ) (L : ℝ≥0) (μ : Measure (Space n))
    (M : ℝ≥0∞) : Set C(Space n, ℝ) :=
  {φ | φ ∈ normalizedConvexLipschitzPotentials n L ∧
    (∀ x, 0 ≤ φ x) ∧ momentDualEnergy μ φ ≤ M}

theorem isCompact_normalizedMomentEnergySublevel (n : ℕ) (L : ℝ≥0)
    (μ : Measure (Space n)) (M : ℝ≥0∞) :
    IsCompact (normalizedMomentEnergySublevel n L μ M) := by
  have hnonneg : IsClosed {φ : C(Space n, ℝ) | ∀ x, 0 ≤ φ x} := by
    have h : ∀ x : Space n, IsClosed {φ : C(Space n, ℝ) | 0 ≤ φ x} :=
      fun x => isClosed_le continuous_const (continuous_eval_const x)
    convert isClosed_iInter h using 1
    ext φ
    simp
  exact (isCompact_normalizedConvexLipschitzPotentials n L).inter_right
    (hnonneg.inter (isClosed_momentDualEnergy_sublevel μ M))

theorem IsIsotropic.tendsto_momentPartitionFunction_of_energy_bound
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    {φ : ℕ → Space n → ℝ} {ψ : Space n → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hφ : ∀ k, AEStronglyMeasurable (φ k) volume)
    (hnonneg : ∀ k x, 0 ≤ φ k x)
    (henergy : ∀ k, momentDualEnergy μ (φ k) ≤ ENNReal.ofReal M)
    (hlim : ∀ x, Tendsto (fun k => φ k x) atTop (𝓝 (ψ x))) :
    Tendsto (fun k => momentPartitionFunction (φ k)) atTop (𝓝 (momentPartitionFunction ψ)) := by
  obtain ⟨a, ha, hcone⟩ := hμ.exists_dualEnergy_linear_coercivity
  have hconek (k : ℕ) (x : Space n) : a * ‖x‖ - M ≤ φ k x := by
    have hkfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (henergy k)
    have hkr := ENNReal.toReal_le_of_le_ofReal hM (henergy k)
    have h := hcone (φ k) (hnonneg k) hkfinite x
    linarith
  apply tendsto_integral_of_dominated_convergence
    (fun x : Space n => Real.exp M * Real.exp (-a * ‖x‖))
  · intro k
    exact Real.continuous_exp.comp_aestronglyMeasurable (hφ k).neg
  · exact (integrable_exp_neg_mul_norm n ha).const_mul _
  · intro k
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := hconek k x
      linarith
  · exact Eventually.of_forall fun x => Real.continuous_exp.continuousAt.tendsto.comp (hlim x).neg

theorem IsIsotropic.momentPartitionFunction_pos_of_finite_energy
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    {φ : Space n → ℝ} (hφ : AEStronglyMeasurable φ volume) (hnonneg : ∀ x, 0 ≤ φ x)
    (hfinite : momentDualEnergy μ φ ≠ ∞) : 0 < momentPartitionFunction φ := by
  obtain ⟨a, ha, hcone⟩ := hμ.exists_dualEnergy_linear_coercivity
  exact integral_exp_pos (integrable_exp_neg_of_linear_coercivity hφ ha (hcone φ hnonneg hfinite))

/-- Genuine coercivity of the normalized variational functional. The constant
depends only on the measure and dimension; the dual energy is not assumed to
control the partition function, but is proved to do so. -/
theorem IsIsotropic.exists_momentVariational_coercivity
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) :
    ∃ C : ℝ, ∀ φ : Space n → ℝ, AEStronglyMeasurable φ volume →
      (∀ x, 0 ≤ φ x) → momentDualEnergy μ φ ≠ ∞ →
      momentVariationalFunctional μ φ ≤ C - (momentDualEnergy μ φ).toReal / 2 := by
  obtain ⟨a, ha, hcone⟩ := hμ.exists_dualEnergy_linear_coercivity
  let J : ℝ := ∫ x : Space n, Real.exp (-(a / 2) * ‖x‖)
  have hJ : 0 < J := integral_exp_neg_mul_norm_pos n (half_pos ha)
  refine ⟨Real.log J, fun φ hφ hnonneg hfinite => ?_⟩
  have hpart := momentPartitionFunction_le_exp_energy_mul_kernel hφ ha hnonneg
    (hcone φ hnonneg hfinite) (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  have hpart' : momentPartitionFunction φ ≤
      Real.exp ((momentDualEnergy μ φ).toReal / 2) * J := by
    simpa only [J, div_eq_mul_inv, one_mul, mul_comm] using hpart
  have hlog := Real.log_le_log (hμ.momentPartitionFunction_pos_of_finite_energy hφ hnonneg hfinite) hpart'
  rw [Real.log_mul (Real.exp_pos _).ne' hJ.ne', Real.log_exp] at hlog
  unfold momentVariationalFunctional
  linarith

theorem IsIsotropic.continuous_partition_on_energy_sublevel
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    (L : ℝ≥0) {M : ℝ} (hM : 0 ≤ M) :
    Continuous (fun φ : normalizedMomentEnergySublevel n L μ (ENNReal.ofReal M) =>
      momentPartitionFunction φ.1) := by
  apply SeqContinuous.continuous
  intro φ ψ hlim
  apply hμ.tendsto_momentPartitionFunction_of_energy_bound hM
    (fun k => (φ k).1.continuous.aestronglyMeasurable)
    (fun k => (φ k).2.2.1) (fun k => (φ k).2.2.2)
  intro x
  exact ((continuous_eval_const x).comp continuous_subtype_val).continuousAt.tendsto.comp hlim

theorem lowerSemicontinuous_dualEnergy_toReal_on_sublevel
    {n : ℕ} (μ : Measure (Space n)) (L : ℝ≥0) (M : ℝ) :
    LowerSemicontinuous
      (fun φ : normalizedMomentEnergySublevel n L μ (ENNReal.ofReal M) =>
        (momentDualEnergy μ φ.1).toReal) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  by_cases hr : 0 ≤ r
  · have heq :
        (fun φ : normalizedMomentEnergySublevel n L μ (ENNReal.ofReal M) =>
          (momentDualEnergy μ φ.1).toReal) ⁻¹' Iic r =
        Subtype.val ⁻¹' {φ : C(Space n, ℝ) | momentDualEnergy μ φ ≤ ENNReal.ofReal r} := by
      ext φ
      exact (ENNReal.le_ofReal_iff_toReal_le
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top φ.2.2.2) hr).symm
    rw [heq]
    exact (isClosed_momentDualEnergy_sublevel μ _).preimage continuous_subtype_val
  · have heq :
        (fun φ : normalizedMomentEnergySublevel n L μ (ENNReal.ofReal M) =>
          (momentDualEnergy μ φ.1).toReal) ⁻¹' Iic r = ∅ := by
      ext φ
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact not_le_of_gt (lt_of_lt_of_le (lt_of_not_ge hr) ENNReal.toReal_nonneg)
    rw [heq]
    exact isClosed_empty

theorem IsIsotropic.upperSemicontinuous_functional_on_energy_sublevel
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    (L : ℝ≥0) {M : ℝ} (hM : 0 ≤ M) :
    UpperSemicontinuous
      (fun φ : normalizedMomentEnergySublevel n L μ (ENNReal.ofReal M) =>
        momentVariationalFunctional μ φ.1) := by
  have hlog : Continuous
      (fun φ : normalizedMomentEnergySublevel n L μ (ENNReal.ofReal M) =>
        Real.log (momentPartitionFunction φ.1)) := by
    apply (hμ.continuous_partition_on_energy_sublevel L hM).log
    intro φ
    exact (hμ.momentPartitionFunction_pos_of_finite_energy φ.1.continuous.aestronglyMeasurable
      φ.2.2.1 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top φ.2.2.2)).ne'
  have hneg := (continuous_neg : Continuous (fun x : ℝ => -x)).comp_lowerSemicontinuous_antitone
    (lowerSemicontinuous_dualEnergy_toReal_on_sublevel μ L M)
    (fun x y hxy => neg_le_neg hxy)
  simpa only [momentVariationalFunctional, sub_eq_add_neg, Function.comp_def] using
    hlog.upperSemicontinuous.add hneg

end KLS
end

#print axioms KLS.isCompact_normalizedMomentEnergySublevel
#print axioms KLS.IsIsotropic.exists_momentVariational_coercivity
#print axioms KLS.IsIsotropic.continuous_partition_on_energy_sublevel
#print axioms KLS.IsIsotropic.upperSemicontinuous_functional_on_energy_sublevel
