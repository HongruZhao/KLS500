import KLS.LogConcavityAbsoluteContinuity
import KLS.LogConcaveDensityPotential
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Measure

/-!
# Interior regularity and concentration of the canonical density

An everywhere-finite pointwise log-concave density has a convex positivity
domain. Its real negative logarithm is convex there and locally Lipschitz on
the interior. For the canonical density of an admissible measure, that interior
is nonempty and carries full measure, since a convex boundary is Lebesgue-null
and absolute continuity has already been proved from compact-set log-concavity.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

noncomputable section
namespace KLS

/-- The finite part of the negative-log density potential. Its values outside
the positive-density domain are not used for convexity or regularity. -/
def realDensityPotential {n : ℕ} (d : Space n → ℝ≥0∞) (x : Space n) : ℝ :=
  -Real.log (d x).toReal

theorem convex_positiveDomain_of_pointwise_logConcave {n : ℕ} {d : Space n → ℝ≥0∞}
    (hlog : ∀ (x y : Space n) (t : ℝ), 0 < t → t < 1 →
      d x ^ t * d y ^ (1 - t) ≤ d (t • x + (1 - t) • y)) :
    Convex ℝ {x | 0 < d x} := by
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hy
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa [hb0, ha1] using hx
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have ha1 : a < 1 := by linarith
  have hba : b = 1 - a := by linarith
  rw [hba]
  exact (ENNReal.mul_pos (ENNReal.rpow_pos_of_nonneg hx ha).ne'
    (ENNReal.rpow_pos_of_nonneg hy (sub_nonneg.mpr ha1.le)).ne').trans_le
    (hlog x y a ha' ha1)

theorem convexOn_realDensityPotential {n : ℕ} {d : Space n → ℝ≥0∞}
    (hfinite : ∀ x, d x < ⊤)
    (hlog : ∀ (x y : Space n) (t : ℝ), 0 < t → t < 1 →
      d x ^ t * d y ^ (1 - t) ≤ d (t • x + (1 - t) • y)) :
    ConvexOn ℝ {x | 0 < d x} (realDensityPotential d) := by
  have hD := convex_positiveDomain_of_pointwise_logConcave hlog
  refine ⟨hD, ?_⟩
  intro x hx y hy a b ha hb hab
  change 0 < d x at hx
  change 0 < d y at hy
  have hc : 0 < d (a • x + b • y) := hD hx hy ha hb hab
  have hxepi : (x, realDensityPotential d x) ∈
      {p : Space n × ℝ | finiteDensityPotential (d p.1) ≤ (p.2 : WithTop ℝ)} := by
    simp [finiteDensityPotential, hx.ne', realDensityPotential]
  have hyepi : (y, realDensityPotential d y) ∈
      {p : Space n × ℝ | finiteDensityPotential (d p.1) ≤ (p.2 : WithTop ℝ)} := by
    simp [finiteDensityPotential, hy.ne', realDensityPotential]
  have h := extendedConvex_finiteDensityPotential hfinite hlog hxepi hyepi ha hb hab
  change finiteDensityPotential (d (a • x + b • y)) ≤
    ((a * realDensityPotential d x + b * realDensityPotential d y : ℝ) : WithTop ℝ) at h
  simpa only [finiteDensityPotential, ite_eq_right hc.ne', WithTop.coe_le_coe,
    realDensityPotential, smul_eq_mul] using h

theorem locallyLipschitzOn_realDensityPotential_interior {n : ℕ} {d : Space n → ℝ≥0∞}
    (hfinite : ∀ x, d x < ⊤)
    (hlog : ∀ (x y : Space n) (t : ℝ), 0 < t → t < 1 →
      d x ^ t * d y ^ (1 - t) ≤ d (t • x + (1 - t) • y)) :
    LocallyLipschitzOn (interior {x | 0 < d x}) (realDensityPotential d) :=
  (convexOn_realDensityPotential hfinite hlog).locallyLipschitzOn_interior

theorem continuousOn_realDensityPotential_interior {n : ℕ} {d : Space n → ℝ≥0∞}
    (hfinite : ∀ x, d x < ⊤)
    (hlog : ∀ (x y : Space n) (t : ℝ), 0 < t → t < 1 →
      d x ^ t * d y ^ (1 - t) ≤ d (t • x + (1 - t) • y)) :
    ContinuousOn (realDensityPotential d) (interior {x | 0 < d x}) :=
  (convexOn_realDensityPotential hfinite hlog).continuousOn_interior

/-- Removing the boundary of a convex positivity domain removes no Lebesgue
measure. This generic statement requires no normalization of the density. -/
theorem volume_frontier_positiveDomain_eq_zero {n : ℕ} {d : Space n → ℝ≥0∞}
    (hlog : ∀ (x y : Space n) (t : ℝ), 0 < t → t < 1 →
      d x ^ t * d y ^ (1 - t) ≤ d (t • x + (1 - t) • y)) :
    volume (frontier {x | 0 < d x}) = 0 :=
  (convex_positiveDomain_of_pointwise_logConcave hlog).addHaar_frontier volume

theorem admissibleMeasure.lowerBallDensity_positive_interior_nonempty
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    (interior {x | 0 < lowerBallDensity μ x}).Nonempty := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hD := convex_positiveDomain_of_pointwise_logConcave
    (fun x y _t ht0 ht1 => hμ.logConcave.lowerBallDensity_logConcave x y ht0 ht1)
  apply hD.interior_nonempty_iff_affineSpan_eq_top.mpr
  apply hμ.isotropic.affineSubspace_eq_top_of_ae_mem
  exact (lowerBallDensity_pos_ae μ).mono (fun x hx => subset_affineSpan ℝ _ hx)

/-- The original admissible measure gives full mass to the open set where its
canonical density is positive. No smoothness or support assumption is added. -/
theorem admissibleMeasure.lowerBallDensity_positive_interior_mem_ae
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    ∀ᵐ x ∂μ, x ∈ interior {y | 0 < lowerBallDensity μ y} := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hf : μ (frontier {x | 0 < lowerBallDensity μ x}) = 0 :=
    hμ.absolutelyContinuousLebesgue (volume_frontier_positiveDomain_eq_zero
      (fun x y _t ht0 ht1 => hμ.logConcave.lowerBallDensity_logConcave x y ht0 ht1))
  filter_upwards [interior_ae_eq_of_null_frontier hf, lowerBallDensity_pos_ae μ] with x hx hp
  exact hx.mpr hp

theorem admissibleMeasure.canonicalPotential_locallyLipschitzOn
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    LocallyLipschitzOn (interior {x | 0 < lowerBallDensity μ x})
      (realDensityPotential (lowerBallDensity μ)) :=
  locallyLipschitzOn_realDensityPotential_interior hμ.lowerBallDensity_lt_top
    (fun x y _t ht0 ht1 => hμ.logConcave.lowerBallDensity_logConcave x y ht0 ht1)

theorem admissibleMeasure.canonicalPotential_continuousOn
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    ContinuousOn (realDensityPotential (lowerBallDensity μ))
      (interior {x | 0 < lowerBallDensity μ x}) :=
  hμ.canonicalPotential_locallyLipschitzOn.continuousOn

end KLS
end

#print axioms KLS.convexOn_realDensityPotential
#print axioms KLS.admissibleMeasure.lowerBallDensity_positive_interior_mem_ae
#print axioms KLS.admissibleMeasure.canonicalPotential_locallyLipschitzOn
