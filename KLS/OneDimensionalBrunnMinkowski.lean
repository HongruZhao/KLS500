import KLS.Definitions

/-!+# The one-dimensional Brunn--Minkowski inequality

For nonempty compact subsets of the real line, two translated copies inside
their sum are disjoint except possibly at one endpoint. Their Lebesgue
measures add. Scaling then gives the sharp one-dimensional arithmetic bound.
This will supply a compact-set log-concavity witness for an isotropic uniform
interval, without assuming the general density-to-measure bridge.
-/

open MeasureTheory Set
open scoped ENNReal Pointwise

noncomputable section
namespace KLS

theorem real_volume_add_ge {E F : Set ℝ} (hE : IsCompact E) (hF : IsCompact F)
    (hneE : E.Nonempty) (hneF : F.Nonempty) :
    volume E + volume F ≤ volume (E + F) := by
  obtain ⟨a, ha⟩ := hE.exists_isGreatest hneE
  obtain ⟨b, hb⟩ := hF.exists_isLeast hneF
  let S := (fun x : ℝ => x + b) '' E
  let T := (fun x : ℝ => a + x) '' F
  have hS : IsCompact S := hE.image (by fun_prop)
  have hT : IsCompact T := hF.image (by fun_prop)
  have hST : S ∩ T ⊆ {a + b} := by
    rintro z ⟨⟨x, hx, rfl⟩, y, hy, hxy⟩
    have hxa := ha.2 hx
    have hby := hb.2 hy
    simp only [mem_singleton_iff]
    linarith
  have hnull : AEDisjoint volume S T := by
    exact measure_mono_null hST (measure_singleton _)
  have hvS : volume S = volume E := by
    simp [S, image_add_right]
  have hvT : volume T = volume F := by
    simp [T, image_add_left]
  have hsub : S ∪ T ⊆ E + F := by
    rintro z (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact add_mem_add hx hb.1
    · exact add_mem_add ha.1 hy
  calc
    volume E + volume F = volume (S ∪ T) := by
      rw [measure_union₀ hT.measurableSet.nullMeasurableSet hnull, hvS, hvT]
    _ ≤ volume (E + F) := measure_mono hsub

theorem real_volume_affineCombination_ge {E F : Set ℝ}
    (hE : IsCompact E) (hF : IsCompact F) (hneE : E.Nonempty) (hneF : F.Nonempty)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ENNReal.ofReal t * volume E + ENNReal.ofReal (1 - t) * volume F ≤
      volume (t • E + (1 - t) • F) := by
  have ht' : 0 < 1 - t := sub_pos.mpr ht1
  have hneA : (t • E).Nonempty := by
    obtain ⟨x, hx⟩ := hneE
    exact ⟨t • x, ⟨x, hx, rfl⟩⟩
  have hneB : ((1 - t) • F).Nonempty := by
    obtain ⟨x, hx⟩ := hneF
    exact ⟨(1 - t) • x, ⟨x, hx, rfl⟩⟩
  have h := real_volume_add_ge (hE.smul t) (hF.smul (1 - t))
    hneA hneB
  simpa only [Measure.addHaar_smul, Module.finrank_self, pow_one,
    abs_of_pos ht0, abs_of_pos ht'] using h

/-- Weighted arithmetic--geometric mean for finite extended nonnegative
numbers; the finite side conditions precede all real conversions. -/
theorem ennreal_geometric_le_weighted_sum {a b : ℝ≥0∞}
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    a ^ t * b ^ (1 - t) ≤ ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * b := by
  have ht' : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hleft : a ^ t * b ^ (1 - t) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg ht0 ha)
      (ENNReal.rpow_ne_top_of_nonneg ht' hb)
  have ha' : ENNReal.ofReal t * a ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha
  have hb' : ENNReal.ofReal (1 - t) * b ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb
  apply (ENNReal.toReal_le_toReal hleft (ENNReal.add_ne_top.mpr ⟨ha', hb'⟩)).mp
  rw [ENNReal.toReal_add ha' hb']
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal ht0, ENNReal.toReal_ofReal ht']
  exact Real.geom_mean_le_arith_mean2_weighted ht0 ht' ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg (by ring)

theorem real_volume_logConcave {E F : Set ℝ} (hE : IsCompact E) (hF : IsCompact F)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (volume E) ^ t * (volume F) ^ (1 - t) ≤ volume (t • E + (1 - t) • F) := by
  by_cases hneE : E.Nonempty
  · by_cases hneF : F.Nonempty
    · exact (ennreal_geometric_le_weighted_sum hE.measure_ne_top hF.measure_ne_top
        ht0.le ht1.le).trans (real_volume_affineCombination_ge hE hF hneE hneF ht0 ht1)
    · rw [Set.not_nonempty_iff_eq_empty.mp hneF]
      simp [ENNReal.zero_rpow_of_pos (sub_pos.mpr ht1)]
  · rw [Set.not_nonempty_iff_eq_empty.mp hneE]
    simp [ENNReal.zero_rpow_of_pos ht0]

end KLS
end

#print axioms KLS.real_volume_add_ge
#print axioms KLS.real_volume_affineCombination_ge
#print axioms KLS.real_volume_logConcave
