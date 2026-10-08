import KLS.IsotropicSupport

/-!
# Support geometry of the full compact-set class

Compact-set log-concavity forces a convex support. Isotropy forces that
support to have full affine span, so the support of an admissible measure
has nonempty interior. These are prerequisites of the density bridge; they
do not by themselves prove absolute continuity or a log-concave density.
-/

open MeasureTheory Set Metric
open scoped ENNReal Topology

namespace KLS

theorem affineSetCombination_closedBall_subset {n : ℕ} (x y : Space n)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (r : ℝ) :
    affineSetCombination t (closedBall x r) (closedBall y r) ⊆
      closedBall (t • x + (1 - t) • y) r := by
  rintro z ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
  rw [mem_closedBall, dist_eq_norm]
  have heq : t • u + (1 - t) • v - (t • x + (1 - t) • y) =
      t • (u - x) + (1 - t) • (v - y) := by
    simp only [smul_sub]
    abel
  rw [heq]
  calc
    ‖t • (u - x) + (1 - t) • (v - y)‖ ≤
        ‖t • (u - x)‖ + ‖(1 - t) • (v - y)‖ := norm_add_le _ _
    _ = t * ‖u - x‖ + (1 - t) * ‖v - y‖ := by
      rw [norm_smul_of_nonneg ht0, norm_smul_of_nonneg (sub_nonneg.mpr ht1)]
    _ ≤ t * r + (1 - t) * r := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall, dist_eq_norm] using hu) ht0)
        (mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall, dist_eq_norm] using hv)
          (sub_nonneg.mpr ht1))
    _ = r := by ring

/-- Positive mass in compact balls interpolates into positive mass around
every convex combination of support points. No density hypothesis is used. -/
theorem measureLogConcave.convex_support {n : ℕ} {μ : Measure (Space n)}
    (hμ : measureLogConcave μ) : Convex ℝ μ.support := by
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
  apply Metric.nhds_basis_closedBall.mem_measureSupport.mpr
  intro r hr
  have hxpos := Metric.nhds_basis_closedBall.mem_measureSupport.mp hx r hr
  have hypos := Metric.nhds_basis_closedBall.mem_measureSupport.mp hy r hr
  have hprod : 0 < (μ (closedBall x r)) ^ a * (μ (closedBall y r)) ^ (1 - a) :=
    ENNReal.mul_pos (ENNReal.rpow_pos_of_nonneg hxpos ha).ne'
      (ENNReal.rpow_pos_of_nonneg hypos (sub_nonneg.mpr ha1.le)).ne'
  exact (hprod.trans_le (hμ _ _ (isCompact_closedBall x r) (isCompact_closedBall y r)
    a ha' ha1)).trans_le
    (measure_mono (affineSetCombination_closedBall_subset x y ha ha1.le r))

/-- The full compact-set admissible class has a convex, full-dimensional
support. Absolute continuity is a further theorem, not a consequence assumed
in this declaration. -/
theorem admissibleMeasure.support_interior_nonempty {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) : (interior μ.support).Nonempty := by
  let : IsProbabilityMeasure μ := hμ.isProb
  exact hμ.logConcave.convex_support.interior_nonempty_iff_affineSpan_eq_top.mpr
    hμ.isotropic.affineSpan_support_eq_top

end KLS

#print axioms KLS.measureLogConcave.convex_support
#print axioms KLS.admissibleMeasure.support_interior_nonempty
