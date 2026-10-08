import KLS.CompactSetQuantile

/-!
# Multiplicative Brunn--Minkowski on the positive real line

Weighted geometric interpolation of the compact-set quantiles expands
distances. A Hausdorff image-measure bound converts this into a Lebesgue
measure bound without requiring continuity of the quantiles.
-/

open MeasureTheory Set Metric
open scoped ENNReal NNReal

noncomputable section
namespace KLS

theorem geometricMean_superadd {a b c d t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    a ^ t * b ^ (1 - t) + c ^ t * d ^ (1 - t) ≤
      (a + c) ^ t * (b + d) ^ (1 - t) := by
  have hA : 0 < a + c := add_pos ha hc
  have hB : 0 < b + d := add_pos hb hd
  have h₁ := Real.geom_mean_le_arith_mean2_weighted ht0 (sub_nonneg.mpr ht1)
    (div_nonneg ha.le hA.le) (div_nonneg hb.le hB.le) (by ring : t + (1 - t) = 1)
  have h₂ := Real.geom_mean_le_arith_mean2_weighted ht0 (sub_nonneg.mpr ht1)
    (div_nonneg hc.le hA.le) (div_nonneg hd.le hB.le) (by ring : t + (1 - t) = 1)
  have hright : t * (a / (a + c)) + (1 - t) * (b / (b + d)) +
      (t * (c / (a + c)) + (1 - t) * (d / (b + d))) = 1 := by
    field_simp
    ring
  have h := add_le_add h₁ h₂
  rw [hright] at h
  rw [Real.div_rpow ha.le hA.le, Real.div_rpow hb.le hB.le,
    Real.div_rpow hc.le hA.le, Real.div_rpow hd.le hB.le,
    div_mul_div_comm, div_mul_div_comm, ← add_div] at h
  exact (div_le_one (mul_pos (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hB _))).mp h

/-- A map from the open unit interval that expands increments by `c`
has image of Lebesgue measure at least `c`. Its image need not be an interval. -/
theorem volume_range_ge_of_increment {q : Ioo (0 : ℝ) 1 → ℝ} {c : ℝ} (hc : 0 < c)
    (hq : ∀ u v : Ioo (0 : ℝ) 1, u ≤ v → c * ((v : ℝ) - (u : ℝ)) ≤ q v - q u) :
    ENNReal.ofReal c ≤ volume (range q) := by
  let K : ℝ≥0 := ⟨c⁻¹, (inv_pos.mpr hc).le⟩
  have hexpand (u v : Ioo (0 : ℝ) 1) :
      c * dist u v ≤ dist (q u) (q v) := by
    simp only [Subtype.dist_eq, Real.dist_eq]
    rcases le_total u v with huv | hvu
    · have h := hq u v huv
      have huv' : (u : ℝ) ≤ (v : ℝ) := huv
      have hqle : q u ≤ q v := by
        have hh : 0 ≤ c * ((v : ℝ) - (u : ℝ)) :=
          mul_nonneg hc.le (sub_nonneg.mpr huv')
        linarith
      rw [abs_of_nonpos (sub_nonpos.mpr huv'), abs_of_nonpos (sub_nonpos.mpr hqle)]
      nlinarith
    · have h := hq v u hvu
      have hvu' : (v : ℝ) ≤ (u : ℝ) := hvu
      have hqle : q v ≤ q u := by
        have hh : 0 ≤ c * ((u : ℝ) - (v : ℝ)) :=
          mul_nonneg hc.le (sub_nonneg.mpr hvu')
        linarith
      rw [abs_of_nonneg (sub_nonneg.mpr hvu'), abs_of_nonneg (sub_nonneg.mpr hqle)]
      exact h
  have hanti : AntilipschitzWith K q := by
    apply AntilipschitzWith.of_le_mul_dist
    intro u v
    change dist u v ≤ c⁻¹ * dist (q u) (q v)
    calc
      dist u v = c⁻¹ * (c * dist u v) := by field_simp
      _ ≤ c⁻¹ * dist (q u) (q v) := mul_le_mul_of_nonneg_left (hexpand u v) (inv_pos.mpr hc).le
  have hsource : (μH[1] : Measure (Ioo (0 : ℝ) 1)) univ = 1 := by
    have h := (isometry_subtype_coe (s := Ioo (0 : ℝ) 1)).hausdorffMeasure_image
      (d := 1) (Or.inl (by norm_num : (0 : ℝ) ≤ 1)) univ
    have hi : ((↑) : Ioo (0 : ℝ) 1 → ℝ) '' univ = Ioo 0 1 := by ext x; simp
    rw [hi, hausdorffMeasure_real, Real.volume_Ioo] at h
    simpa using h.symm
  have h := hanti.le_hausdorffMeasure_image (d := 1) (by norm_num) univ
  rw [hsource, ENNReal.rpow_one, hausdorffMeasure_real, image_univ] at h
  have hK : (K : ℝ≥0∞) = ENNReal.ofReal c⁻¹ := by
    change (K : ℝ≥0∞) = ENNReal.ofReal (K : ℝ)
    exact ENNReal.ofReal_coe_nnreal.symm
  rw [hK, ENNReal.ofReal_inv_of_pos hc] at h
  have h' := mul_le_mul_right h (ENNReal.ofReal c)
  simpa only [mul_one, ← mul_assoc, ENNReal.mul_inv_cancel
    (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top, one_mul] using h'

def geometricSetCombination (t : ℝ) (E F : Set ℝ) : Set ℝ :=
  (fun p : ℝ × ℝ => p.1 ^ t * p.2 ^ (1 - t)) '' (E ×ˢ F)

/-- The one-dimensional multiplicative Brunn--Minkowski inequality for
arbitrary compact subsets of the positive half-line. -/
theorem real_volume_geometricCombination_ge {E F : Set ℝ}
    (hE : IsCompact E) (hF : IsCompact F)
    (hEp : E ⊆ Ioi 0) (hFp : F ⊆ Ioi 0) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    (volume E) ^ t * (volume F) ^ (1 - t) ≤
      volume (geometricSetCombination t E F) := by
  by_cases hEz : volume E = 0
  · simp [hEz, ENNReal.zero_rpow_of_pos ht0]
  by_cases hFz : volume F = 0
  · simp [hFz, ENNReal.zero_rpow_of_pos (sub_pos.mpr ht1)]
  have hA : 0 < volume.real E := ENNReal.toReal_pos hEz hE.measure_ne_top
  have hB : 0 < volume.real F := ENNReal.toReal_pos hFz hF.measure_ne_top
  let qA := compactQuantile hE hA
  let qB := compactQuantile hF hB
  let q : Ioo (0 : ℝ) 1 → ℝ := fun u => qA u ^ t * qB u ^ (1 - t)
  let c : ℝ := volume.real E ^ t * volume.real F ^ (1 - t)
  have hc : 0 < c := mul_pos (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hB _)
  have hqAp (u : Ioo (0 : ℝ) 1) : 0 < qA u := hEp (compactQuantile_mem hE hA u)
  have hqBp (u : Ioo (0 : ℝ) 1) : 0 < qB u := hFp (compactQuantile_mem hF hB u)
  have hinc : ∀ u v : Ioo (0 : ℝ) 1, u ≤ v →
      c * ((v : ℝ) - (u : ℝ)) ≤ q v - q u := by
    intro u v huv
    rcases eq_or_lt_of_le huv with heq | hlt
    · subst v
      simp
    have hd : 0 < (v : ℝ) - (u : ℝ) := sub_pos.mpr hlt
    have hqa := compactQuantile_increment hE hA huv
    have hqb := compactQuantile_increment hF hB huv
    have hsuper := geometricMean_superadd (hqAp u) (hqBp u)
      (mul_pos hA hd) (mul_pos hB hd) ht0.le ht1.le
    have hmono : (qA u + volume.real E * ((v : ℝ) - (u : ℝ))) ^ t *
        (qB u + volume.real F * ((v : ℝ) - (u : ℝ))) ^ (1 - t) ≤ q v := by
      change _ ≤ qA v ^ t * qB v ^ (1 - t)
      have hsA : 0 ≤ qA u + volume.real E * ((v : ℝ) - (u : ℝ)) :=
        add_nonneg (hqAp u).le (mul_nonneg hA.le hd.le)
      have hsB : 0 ≤ qB u + volume.real F * ((v : ℝ) - (u : ℝ)) :=
        add_nonneg (hqBp u).le (mul_nonneg hB.le hd.le)
      apply mul_le_mul
        (Real.rpow_le_rpow hsA (by dsimp [qA]; linarith) ht0.le)
        (Real.rpow_le_rpow hsB (by dsimp [qB]; linarith)
          (sub_nonneg.mpr ht1.le))
        (Real.rpow_nonneg hsB _) (Real.rpow_nonneg (hqAp v).le _)
    have hscale : (volume.real E * ((v : ℝ) - (u : ℝ))) ^ t *
        (volume.real F * ((v : ℝ) - (u : ℝ))) ^ (1 - t) = c * ((v : ℝ) - (u : ℝ)) := by
      rw [Real.mul_rpow hA.le hd.le, Real.mul_rpow hB.le hd.le]
      calc
        volume.real E ^ t * ((v : ℝ) - (u : ℝ)) ^ t *
            (volume.real F ^ (1 - t) * ((v : ℝ) - (u : ℝ)) ^ (1 - t)) =
            c * (((v : ℝ) - (u : ℝ)) ^ t * ((v : ℝ) - (u : ℝ)) ^ (1 - t)) := by
          dsimp [c]
          ring
        _ = c * ((v : ℝ) - (u : ℝ)) := by
          rw [← Real.rpow_add hd, show t + (1 - t) = 1 by ring, Real.rpow_one]
    rw [hscale] at hsuper
    change q u + c * ((v : ℝ) - (u : ℝ)) ≤ _ at hsuper
    linarith
  have hrange : range q ⊆ geometricSetCombination t E F := by
    rintro z ⟨u, rfl⟩
    exact ⟨(qA u, qB u), ⟨compactQuantile_mem hE hA u, compactQuantile_mem hF hB u⟩, rfl⟩
  have h := (volume_range_ge_of_increment hc hinc).trans (measure_mono hrange)
  have hcval : ENNReal.ofReal c = (volume E) ^ t * (volume F) ^ (1 - t) := by
    dsimp [c]
    rw [ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_rpow_of_pos hA,
      ← ENNReal.ofReal_rpow_of_pos hB, ofReal_measureReal hE.measure_ne_top,
      ofReal_measureReal hF.measure_ne_top]
  rwa [hcval] at h

end KLS
end

#print axioms KLS.geometricMean_superadd
#print axioms KLS.volume_range_ge_of_increment
#print axioms KLS.real_volume_geometricCombination_ge
