import KLS.ThirdCumulant
import Mathlib.Topology.Order.Compact

/-!
# Nondegeneracy and coercivity of isotropic affine projections

These statements supply a genuine elementary coercivity input for moment-measure
variational arguments. They construct a positive uniform constant from isotropy.
They do not assume or construct a moment map, a variational optimizer, or any
Monge--Ampere regularity theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

noncomputable section
namespace KLS

/-- The first absolute moment of a linear projection. -/
def projectionAbsoluteMoment {n : ℕ} (μ : Measure (Space n)) (u : Space n) : ℝ :=
  ∫ x, |inner ℝ x u| ∂μ

/-- The first absolute moment of an affine projection. -/
def affineProjectionAbsoluteMoment {n : ℕ} (μ : Measure (Space n))
    (u : Space n) (c : ℝ) : ℝ :=
  ∫ x, |inner ℝ x u - c| ∂μ

theorem IsIsotropic.integrable_inner {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) (u : Space n) :
    Integrable (fun x : Space n => inner ℝ x u) μ :=
  (hμ.memLp_inner u).integrable one_le_two

theorem IsIsotropic.integrable_affineProjection {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) (u : Space n) (c : ℝ) :
    Integrable (fun x : Space n => inner ℝ x u - c) μ :=
  (hμ.integrable_inner u).sub (integrable_const c)

theorem projectionAbsoluteMoment_nonneg {n : ℕ} (μ : Measure (Space n)) (u : Space n) :
    0 ≤ projectionAbsoluteMoment μ u :=
  integral_nonneg fun _x => abs_nonneg _

theorem affineProjectionAbsoluteMoment_nonneg {n : ℕ} (μ : Measure (Space n))
    (u : Space n) (c : ℝ) : 0 ≤ affineProjectionAbsoluteMoment μ u c :=
  integral_nonneg fun _x => abs_nonneg _

theorem projectionAbsoluteMoment_smul {n : ℕ} (μ : Measure (Space n))
    (a : ℝ) (u : Space n) :
    projectionAbsoluteMoment μ (a • u) = |a| * projectionAbsoluteMoment μ u := by
  simp only [projectionAbsoluteMoment, inner_smul_right, abs_mul, integral_const_mul]

/-- Nonzero isotropic projections cannot have vanishing absolute first moment. -/
theorem IsIsotropic.projectionAbsoluteMoment_pos {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) {u : Space n} (hu : u ≠ 0) :
    0 < projectionAbsoluteMoment μ u := by
  have hn := projectionAbsoluteMoment_nonneg μ u
  apply lt_of_le_of_ne hn
  intro hz
  have hae : (fun x : Space n => |inner ℝ x u|) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => abs_nonneg _)
      (hμ.integrable_inner u).abs).mp hz.symm
  have hs : (∫ x : Space n, (inner ℝ x u) ^ 2 ∂μ) = 0 := by
    calc
      _ = ∫ _ : Space n, (0 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hae] with x hx
        have hx' : inner ℝ x u = 0 := abs_eq_zero.mp hx
        simp [hx']
      _ = 0 := integral_zero _ _
  rw [hμ.integral_inner_sq] at hs
  exact hu (norm_eq_zero.mp (sq_eq_zero_iff.mp hs))

/-- Dependence of the projection moment on its direction is Lipschitz. -/
theorem IsIsotropic.projectionAbsoluteMoment_sub_le {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) (u v : Space n) :
    |projectionAbsoluteMoment μ u - projectionAbsoluteMoment μ v| ≤
      (∫ x : Space n, ‖x‖ ∂μ) * ‖u - v‖ := by
  have hfu := (hμ.integrable_inner u).abs
  have hfv := (hμ.integrable_inner v).abs
  unfold projectionAbsoluteMoment
  rw [← integral_sub hfu hfv]
  calc
    _ ≤ ∫ x : Space n, |(|inner ℝ x u| - |inner ℝ x v|)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x : Space n, ‖x‖ * ‖u - v‖ ∂μ := by
      apply integral_mono (hfu.sub hfv).abs (hμ.1.norm.mul_const _)
      intro x
      calc
        _ ≤ |inner ℝ x u - inner ℝ x v| := abs_abs_sub_abs_le_abs_sub _ _
        _ = |inner ℝ x (u - v)| := by rw [inner_sub_right]
        _ ≤ ‖x‖ * ‖u - v‖ := abs_real_inner_le_norm _ _
    _ = _ := integral_mul_const _ _

theorem IsIsotropic.continuous_projectionAbsoluteMoment {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) :
    Continuous (projectionAbsoluteMoment μ) := by
  let K : ℝ≥0 := ⟨∫ x : Space n, ‖x‖ ∂μ, integral_nonneg (fun _x => norm_nonneg _)⟩
  have hLip : LipschitzWith K (projectionAbsoluteMoment μ) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    change dist (projectionAbsoluteMoment μ u) (projectionAbsoluteMoment μ v) ≤
      (∫ x : Space n, ‖x‖ ∂μ) * dist u v
    simpa only [dist_eq_norm, Real.norm_eq_abs] using hμ.projectionAbsoluteMoment_sub_le u v
  exact hLip.continuous

/-- Compactness of the unit sphere upgrades directional positivity to a
uniform positive lower bound. This also holds in dimension zero. -/
theorem IsIsotropic.exists_projectionAbsoluteMoment_coercivity
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) :
    ∃ m : ℝ, 0 < m ∧ ∀ u : Space n, m * ‖u‖ ≤ projectionAbsoluteMoment μ u := by
  obtain ⟨m, hm, hbound⟩ := (isCompact_sphere (0 : Space n) 1).exists_forall_le'
    hμ.continuous_projectionAbsoluteMoment.continuousOn (a := 0) (by
      intro u hu
      apply hμ.projectionAbsoluteMoment_pos
      intro hz
      simp [hz] at hu)
  refine ⟨m, hm, fun u => ?_⟩
  by_cases hu : u = 0
  · simp [hu, projectionAbsoluteMoment]
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hunit : ‖(‖u‖⁻¹ : ℝ) • u‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm), inv_mul_cancel₀ hnorm.ne']
  have h := hbound ((‖u‖⁻¹ : ℝ) • u) (by simpa only [Metric.mem_sphere,
    dist_zero_right] using hunit)
  rw [projectionAbsoluteMoment_smul, abs_of_pos (inv_pos.mpr hnorm)] at h
  have hmul := mul_le_mul_of_nonneg_right h (le_of_lt hnorm)
  simpa only [mul_assoc, mul_left_comm ‖u‖⁻¹, inv_mul_cancel₀ hnorm.ne',
    mul_one, one_mul] using hmul

/-- Centering prevents an affine offset from making its absolute moment small. -/
theorem IsIsotropic.abs_offset_le_affineProjectionAbsoluteMoment
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    (u : Space n) (c : ℝ) : |c| ≤ affineProjectionAbsoluteMoment μ u c := by
  have h := abs_integral_le_integral_abs (μ := μ) (f := fun x : Space n => inner ℝ x u - c)
  rw [integral_sub (hμ.integrable_inner u) (integrable_const c), hμ.integral_inner] at h
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul,
    zero_sub, abs_neg, affineProjectionAbsoluteMoment] using h

theorem IsIsotropic.projectionAbsoluteMoment_le_twice_affine
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    (u : Space n) (c : ℝ) :
    projectionAbsoluteMoment μ u ≤ 2 * affineProjectionAbsoluteMoment μ u c := by
  have htri : projectionAbsoluteMoment μ u ≤ affineProjectionAbsoluteMoment μ u c + |c| := by
    calc
      _ ≤ ∫ x : Space n, (|inner ℝ x u - c| + |c|) ∂μ := by
        apply integral_mono (hμ.integrable_inner u).abs
          ((hμ.integrable_affineProjection u c).abs.add (integrable_const _))
        intro x
        calc
          |inner ℝ x u| = |(inner ℝ x u - c) + c| := by congr 1; ring
          _ ≤ |inner ℝ x u - c| + |c| := abs_add_le _ _
      _ = _ := by
        rw [integral_add (hμ.integrable_affineProjection u c).abs (integrable_const _)]
        simp only [affineProjectionAbsoluteMoment, integral_const,
          probReal_univ, smul_eq_mul, one_mul]
  have hoff := hμ.abs_offset_le_affineProjectionAbsoluteMoment u c
  linarith

/-- A simultaneous coercive bound on direction and offset. This is an actual
positive constant obtained from isotropy, with no variational-existence premise. -/
theorem IsIsotropic.exists_affineProjectionAbsoluteMoment_coercivity
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) :
    ∃ m : ℝ, 0 < m ∧ ∀ (u : Space n) (c : ℝ),
      m * ‖u‖ + |c| ≤ 3 * affineProjectionAbsoluteMoment μ u c := by
  obtain ⟨m, hm, hbound⟩ := hμ.exists_projectionAbsoluteMoment_coercivity
  refine ⟨m, hm, fun u c => ?_⟩
  have hdir := (hbound u).trans (hμ.projectionAbsoluteMoment_le_twice_affine u c)
  have hoff := hμ.abs_offset_le_affineProjectionAbsoluteMoment u c
  linarith

/-- In particular the absolute affine projection is bounded away from zero,
uniformly over every unit direction and every real offset. -/
theorem IsIsotropic.exists_uniform_affineProjectionAbsoluteMoment_pos
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) :
    ∃ m : ℝ, 0 < m ∧ ∀ (u : Space n) (c : ℝ), ‖u‖ = 1 →
      m ≤ affineProjectionAbsoluteMoment μ u c := by
  obtain ⟨m, hm, hbound⟩ := hμ.exists_projectionAbsoluteMoment_coercivity
  refine ⟨m / 2, half_pos hm, fun u c hu => ?_⟩
  have hdir := (hbound u).trans (hμ.projectionAbsoluteMoment_le_twice_affine u c)
  rw [hu, mul_one] at hdir
  linarith

/-- Bounded support gives an explicit coercivity constant from second moments.
No smooth density or log-concavity assumption is needed. -/
theorem IsIsotropic.norm_le_radius_mul_projectionAbsoluteMoment
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    {R : ℝ} (hbound : ∀ᵐ x ∂μ, ‖x‖ ≤ R) (u : Space n) :
    ‖u‖ ≤ R * projectionAbsoluteMoment μ u := by
  by_cases hu : u = 0
  · simp [hu, projectionAbsoluteMoment]
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hsecond : ‖u‖ ^ 2 ≤ (R * ‖u‖) * projectionAbsoluteMoment μ u := by
    rw [← hμ.integral_inner_sq]
    unfold projectionAbsoluteMoment
    rw [← integral_const_mul]
    apply integral_mono_ae (hμ.memLp_inner u).integrable_sq
      ((hμ.integrable_inner u).abs.const_mul _)
    filter_upwards [hbound] with x hx
    have hproj : |inner ℝ x u| ≤ R * ‖u‖ :=
      (abs_real_inner_le_norm x u).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
    calc
      (inner ℝ x u) ^ 2 = |inner ℝ x u| * |inner ℝ x u| := by rw [← pow_two, sq_abs]
      _ ≤ (R * ‖u‖) * |inner ℝ x u| := mul_le_mul_of_nonneg_right hproj (abs_nonneg _)
  have hprod : ‖u‖ * ‖u‖ ≤ (R * projectionAbsoluteMoment μ u) * ‖u‖ := by
    nlinarith only [hsecond]
  exact (mul_le_mul_iff_left₀ hnorm).mp (by simpa only [mul_comm] using hprod)

theorem IsIsotropic.norm_le_twice_radius_mul_affineProjectionAbsoluteMoment
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ᵐ x ∂μ, ‖x‖ ≤ R) (u : Space n) (c : ℝ) :
    ‖u‖ ≤ (2 * R) * affineProjectionAbsoluteMoment μ u c := by
  have h := (hμ.norm_le_radius_mul_projectionAbsoluteMoment hbound u).trans
    (mul_le_mul_of_nonneg_left (hμ.projectionAbsoluteMoment_le_twice_affine u c) hR)
  simpa only [← mul_assoc, mul_comm R 2] using h

end KLS
end

#print axioms KLS.IsIsotropic.exists_projectionAbsoluteMoment_coercivity
#print axioms KLS.IsIsotropic.exists_affineProjectionAbsoluteMoment_coercivity
#print axioms KLS.IsIsotropic.exists_uniform_affineProjectionAbsoluteMoment_pos
#print axioms KLS.IsIsotropic.norm_le_twice_radius_mul_affineProjectionAbsoluteMoment
