import KLS.OneDimensionalBrunnMinkowski
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Quantile selection for arbitrary compact real sets

Cumulative Lebesgue mass is monotone and one-Lipschitz. Every intermediate
mass has a representative in the compact set itself, including sets with
gaps or empty interior. The selected representatives increase by at least
their mass difference. No regularity of a quantile derivative is assumed.
-/

open MeasureTheory Set Metric
open scoped ENNReal

noncomputable section
namespace KLS

def compactCumulative (E : Set ℝ) (x : ℝ) : ℝ := volume.real (E ∩ Iic x)

theorem compactCumulative_mono {E : Set ℝ} (hE : IsCompact E) :
    Monotone (compactCumulative E) := by
  intro x y hxy
  exact measureReal_mono (inter_subset_inter_right _ (Iic_subset_Iic.mpr hxy))
    (measure_ne_top_of_subset inter_subset_left hE.measure_ne_top)

theorem compactCumulative_sub_le {E : Set ℝ} (hE : IsCompact E) {x y : ℝ}
    (hxy : x ≤ y) : compactCumulative E y - compactCumulative E x ≤ y - x := by
  have hdecomp : E ∩ Iic y = (E ∩ Iic x) ∪ (E ∩ Ioc x y) := by
    ext z
    simp only [mem_inter_iff, mem_Iic, mem_union, mem_Ioc]
    constructor
    · rintro ⟨hzE, hzy⟩
      by_cases hzx : z ≤ x
      · exact Or.inl ⟨hzE, hzx⟩
      · exact Or.inr ⟨hzE, lt_of_not_ge hzx, hzy⟩
    · rintro (⟨hzE, hzx⟩ | ⟨hzE, hzx, hzy⟩)
      · exact ⟨hzE, hzx.trans hxy⟩
      · exact ⟨hzE, hzy⟩
  have hdisj : Disjoint (E ∩ Iic x) (E ∩ Ioc x y) := by
    rw [disjoint_left]
    intro z hz hz'
    exact (not_lt_of_ge hz.2) hz'.2.1
  have hmass : compactCumulative E y = compactCumulative E x +
      volume.real (E ∩ Ioc x y) := by
    unfold compactCumulative
    rw [hdecomp, measureReal_union hdisj (hE.measurableSet.inter measurableSet_Ioc)
      (measure_ne_top_of_subset inter_subset_left hE.measure_ne_top)
      (measure_ne_top_of_subset inter_subset_left hE.measure_ne_top)]
  have hle : volume.real (E ∩ Ioc x y) ≤ y - x := by
    simpa only [Real.volume_real_Ioc_of_le hxy] using
      (measureReal_mono (μ := (volume : Measure ℝ)) (s₁ := E ∩ Ioc x y)
        (s₂ := Ioc x y) inter_subset_right (by simp))
  linarith

theorem compactCumulative_lipschitz {E : Set ℝ} (hE : IsCompact E) :
    LipschitzWith 1 (compactCumulative E) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr (compactCumulative_mono hE hxy)),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith [compactCumulative_sub_le hE hxy]
  · rw [abs_of_nonneg (sub_nonneg.mpr (compactCumulative_mono hE hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact compactCumulative_sub_le hE hyx

/-- Every strict intermediate cumulative mass can be reached at a point of
the compact set, even if the original intermediate-value point lies in a gap. -/
theorem exists_mem_compactCumulative_eq {E : Set ℝ} (hE : IsCompact E)
    {m : ℝ} (hm0 : 0 < m) (hmE : m < volume.real E) :
    ∃ x ∈ E, compactCumulative E x = m := by
  have hne : E.Nonempty := nonempty_of_measureReal_ne_zero (by linarith)
  obtain ⟨a, ha⟩ := hE.exists_isLeast hne
  obtain ⟨b, hb⟩ := hE.exists_isGreatest hne
  have hca : compactCumulative E a = 0 := by
    have hsub : E ∩ Iic a ⊆ {a} := by
      rintro z ⟨hzE, hza⟩
      exact mem_singleton_iff.mpr (le_antisymm hza (ha.2 hzE))
    exact measureReal_mono_null hsub (by simp [Measure.real]) (by simp)
  have hcb : compactCumulative E b = volume.real E := by
    unfold compactCumulative
    rw [inter_eq_left.mpr (show E ⊆ Iic b from hb.2)]
  obtain ⟨x, hx, hcx⟩ := intermediate_value_Icc (ha.2 hb.1)
    (compactCumulative_lipschitz hE).continuous.continuousOn
    (show m ∈ Icc (compactCumulative E a) (compactCumulative E b) by
      rw [hca, hcb]
      exact ⟨hm0.le, hmE.le⟩)
  have hK : IsCompact (E ∩ Iic x) := hE.inter_right isClosed_Iic
  have hKne : (E ∩ Iic x).Nonempty :=
    nonempty_of_measureReal_ne_zero (by change compactCumulative E x ≠ 0; rw [hcx]; linarith)
  obtain ⟨q, hq⟩ := hK.exists_isGreatest hKne
  refine ⟨q, hq.1.1, ?_⟩
  have heq : E ∩ Iic q = E ∩ Iic x := by
    apply Subset.antisymm
    · exact inter_subset_inter_right _ (Iic_subset_Iic.mpr hq.1.2)
    · intro z hz
      exact ⟨hz.1, hq.2 hz⟩
  simpa only [compactCumulative, heq] using hcx

/-- A selected point of a compact set with a prescribed proportion of its mass. -/
def compactQuantile {E : Set ℝ} (hE : IsCompact E) (hpos : 0 < volume.real E)
    (u : Ioo (0 : ℝ) 1) : ℝ :=
  Classical.choose (exists_mem_compactCumulative_eq hE
    (mul_pos hpos u.2.1) (by nlinarith [u.2.2]))

theorem compactQuantile_mem {E : Set ℝ} (hE : IsCompact E) (hpos : 0 < volume.real E)
    (u : Ioo (0 : ℝ) 1) : compactQuantile hE hpos u ∈ E :=
  (Classical.choose_spec (exists_mem_compactCumulative_eq hE
    (mul_pos hpos u.2.1) (by nlinarith [u.2.2]))).1

theorem compactCumulative_compactQuantile {E : Set ℝ} (hE : IsCompact E)
    (hpos : 0 < volume.real E) (u : Ioo (0 : ℝ) 1) :
    compactCumulative E (compactQuantile hE hpos u) = volume.real E * (u : ℝ) :=
  (Classical.choose_spec (exists_mem_compactCumulative_eq hE
    (mul_pos hpos u.2.1) (by nlinarith [u.2.2]))).2

theorem compactQuantile_strictMono {E : Set ℝ} (hE : IsCompact E)
    (hpos : 0 < volume.real E) : StrictMono (compactQuantile hE hpos) := by
  intro u v huv
  change (u : ℝ) < (v : ℝ) at huv
  by_contra h
  have hm := compactCumulative_mono hE (le_of_not_gt h)
  rw [compactCumulative_compactQuantile, compactCumulative_compactQuantile] at hm
  exact (not_le_of_gt (mul_lt_mul_of_pos_left huv hpos)) hm

/-- Quantiles cannot compress distances by more than the total set mass. -/
theorem compactQuantile_increment {E : Set ℝ} (hE : IsCompact E)
    (hpos : 0 < volume.real E) {u v : Ioo (0 : ℝ) 1} (huv : u ≤ v) :
    volume.real E * ((v : ℝ) - (u : ℝ)) ≤
      compactQuantile hE hpos v - compactQuantile hE hpos u := by
  have h := compactCumulative_sub_le hE ((compactQuantile_strictMono hE hpos).monotone huv)
  rw [compactCumulative_compactQuantile, compactCumulative_compactQuantile] at h
  linarith

end KLS
end

#print axioms KLS.exists_mem_compactCumulative_eq
#print axioms KLS.compactQuantile_increment
