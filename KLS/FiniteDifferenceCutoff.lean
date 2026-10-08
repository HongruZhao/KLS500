import KLS.FiniteDifferenceMollification
import KLS.WeightedFaithfulCutoff

/-! # Actual compact localization of L2 finite-difference bounds -/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff ENNReal NNReal Topology Pointwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

theorem coordinateDifferenceQuotient_mul (χ f : Space n → ℝ) (i : Fin n) (t : ℝ) (x : Space n) :
    coordinateDifferenceQuotient (fun y => χ y * f y) i t x =
      χ x * coordinateDifferenceQuotient f i t x +
        f (x + t • EuclideanSpace.single i 1) * coordinateDifferenceQuotient χ i t x := by
  unfold coordinateDifferenceQuotient
  ring

theorem coordinateDifferenceQuotient_lipschitz_bound {χ : Space n → ℝ} {D : ℝ≥0}
    (hχ : LipschitzWith D χ) (i : Fin n) {t : ℝ} (ht : t ≠ 0) (x : Space n) :
    ‖coordinateDifferenceQuotient χ i t x‖ ≤ D := by
  have hb := hχ.norm_sub_le (x + t • EuclideanSpace.single i 1) x
  have hn : ‖(x + t • EuclideanSpace.single i 1) - x‖ = |t| := by
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, PiLp.norm_single,
      norm_one, mul_one]
  rw [hn] at hb
  unfold coordinateDifferenceQuotient
  rw [norm_mul, norm_inv]
  calc
    _ ≤ |t|⁻¹ * ((D : ℝ) * |t|) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (abs_nonneg t))
    _ = D := by rw [mul_left_comm, inv_mul_cancel₀ (abs_ne_zero.mpr ht), mul_one]

theorem coordinateDifferenceQuotient_eq_zero_outside_enlargement
    {χ : Space n → ℝ} (i : Fin n) (m : ℕ) {x : Space n}
    (hx : x ∉ mollifierEnlargement (tsupport χ)) :
    coordinateDifferenceQuotient χ i (cutoffScale m) x = 0 := by
  have hχx : χ x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    apply hx
    have he := Set.add_mem_add h (show (0 : Space n) ∈ closedBall (0 : Space n) 2 by simp)
    simpa only [mollifierEnlargement, add_zero] using he
  have hs : χ (x + cutoffScale m • EuclideanSpace.single i 1) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    apply hx
    have hv : -(cutoffScale m • EuclideanSpace.single i 1) ∈ closedBall (0 : Space n) 2 := by
      simp only [mem_closedBall, dist_zero_right, norm_neg, norm_smul, Real.norm_eq_abs,
        abs_of_pos (cutoffScale_pos m), PiLp.norm_single, norm_one, mul_one]
      exact (cutoffScale_le_one m).trans (by norm_num)
    have he := Set.add_mem_add h hv
    simpa only [mollifierEnlargement, add_neg_cancel_right] using he
  simp only [coordinateDifferenceQuotient, hs, hχx, sub_self, mul_zero]

theorem exists_cutoff_weak_coordinateDerivative_of_weighted_difference_bound
    {f χ : Space n → ℝ} (hf : AEStronglyMeasurable f volume) {B : ℝ} (hB : 0 ≤ B)
    (hfB : ∀ᵐ x ∂volume, ‖f x‖ ≤ B) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (i : Fin n) {A : ℝ}
    (hA : ∀ m, eLpNorm (fun x => χ x * coordinateDifferenceQuotient f i (cutoffScale m) x)
      2 volume ≤ ENNReal.ofReal A) :
    ∃ g : Lp ℝ 2 (volume : Measure (Space n)),
      HasWeakCoordinateDerivative (fun x => χ x * f x) i g := by
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hχ (by norm_num)
  let K := mollifierEnlargement (tsupport χ)
  have hK : IsCompact K := isCompact_mollifierEnlargement hc
  let d : Space n → ℝ := K.indicator (fun _ => (D : ℝ))
  have hd : MemLp d 2 volume :=
    memLp_indicator_const 2 hK.measurableSet.nullMeasurableSet (D : ℝ) (Or.inr hK.measure_lt_top.ne)
  have hfTop : MemLp f ∞ volume := memLp_top_of_bound hf B hfB
  have hχ2 : MemLp χ 2 volume := hχ.continuous.memLp_of_hasCompactSupport hc
  have hχf : MemLp (fun x => χ x * f x) 2 volume :=
    hχ2.mul hfTop
  let C : ℝ≥0∞ := ENNReal.ofReal A + ENNReal.ofReal B * eLpNorm d 2 volume
  have hC : C ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hd.eLpNorm_ne_top⟩
  have hbound (m : ℕ) :
      eLpNorm (coordinateDifferenceQuotient (fun x => χ x * f x) i (cutoffScale m)) 2 volume ≤ C := by
    let s : Space n → ℝ := fun x => f (x + cutoffScale m • EuclideanSpace.single i 1) *
      coordinateDifferenceQuotient χ i (cutoffScale m) x
    have hshift : ∀ᵐ x ∂volume, ‖f (x + cutoffScale m • EuclideanSpace.single i 1)‖ ≤ B :=
      (measurePreserving_add_right volume (cutoffScale m • EuclideanSpace.single i 1)).quasiMeasurePreserving.ae hfB
    have hsm : AEStronglyMeasurable s volume :=
      (hf.comp_measurePreserving (measurePreserving_add_right volume
        (cutoffScale m • EuclideanSpace.single i 1))).mul
        (memLp_coordinateDifferenceQuotient (hχ.continuous.memLp_of_hasCompactSupport hc) i _).aestronglyMeasurable
    have hs : eLpNorm s 2 volume ≤ ENNReal.ofReal B * eLpNorm d 2 volume := by
      have hm : eLpNorm s 2 volume ≤ eLpNorm (fun x => B * d x) 2 volume := by
        apply eLpNorm_mono_ae hsm
        filter_upwards [hshift] with x hx
        by_cases hxK : x ∈ K
        · have hb := coordinateDifferenceQuotient_lipschitz_bound hD i (cutoffScale_pos m).ne' x
          simp only [s, d, indicator_of_mem hxK, norm_mul, Real.norm_eq_abs,
            abs_of_nonneg hB, abs_of_nonneg D.coe_nonneg]
          simp only [Real.norm_eq_abs] at hx hb
          exact mul_le_mul hx hb (abs_nonneg _) hB
        · have hz := coordinateDifferenceQuotient_eq_zero_outside_enlargement i m hxK
          simp only [s, hz, mul_zero, norm_zero, d, indicator_of_notMem hxK,
            mul_zero, norm_zero, le_refl]
      calc
        _ ≤ eLpNorm (fun x => B * d x) 2 volume := hm
        _ = ENNReal.ofReal B * eLpNorm d 2 volume := by
          change eLpNorm (B • d) 2 volume = _
          rw [eLpNorm_const_smul]
          simp only [Real.enorm_eq_ofReal_abs, abs_of_nonneg hB]
    have he : coordinateDifferenceQuotient (fun x => χ x * f x) i (cutoffScale m) =
        (fun x => χ x * coordinateDifferenceQuotient f i (cutoffScale m) x) + s :=
      funext fun x => coordinateDifferenceQuotient_mul χ f i _ x
    rw [he]
    exact (eLpNorm_add_le (by norm_num)).trans (add_le_add (hA m) hs)
  obtain ⟨g, -, hg⟩ := exists_weak_coordinateDerivative_of_difference_bound hχf hc.mul_right i
    ENNReal.toReal_nonneg (fun m => by
      rw [ENNReal.ofReal_toReal hC]
      exact hbound m)
  exact ⟨g, hg⟩

theorem eLpNorm_weighted_differenceQuotient_le_of_energy
    {f χ : Space n → ℝ} (hf : AEStronglyMeasurable f volume) {B : ℝ}
    (hfB : ∀ᵐ x ∂volume, ‖f x‖ ≤ B) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (i : Fin n) {M : ℝ}
    (henergy : ∀ m, (∫ x, χ x ^ 2 *
      (f (x + cutoffScale m • EuclideanSpace.single i 1) - f x) ^ 2) ≤
      M * cutoffScale m ^ 2) (m : ℕ) :
    eLpNorm (fun x => χ x * coordinateDifferenceQuotient f i (cutoffScale m) x)
      2 volume ≤ ENNReal.ofReal (Real.sqrt M) := by
  have hfTop : MemLp f ∞ volume := memLp_top_of_bound hf B hfB
  have hχ2 : MemLp χ 2 volume := hχ.memLp_of_hasCompactSupport hc
  have hshift := hfTop.comp_measurePreserving
    (measurePreserving_add_right volume (cutoffScale m • EuclideanSpace.single i 1))
  have hq : MemLp (fun x => χ x * coordinateDifferenceQuotient f i (cutoffScale m) x)
      2 volume := hχ2.mul ((hshift.sub hfTop).const_mul _)
  have he : (∫ x, (χ x * coordinateDifferenceQuotient f i (cutoffScale m) x) ^ 2) =
      (cutoffScale m)⁻¹ ^ 2 * (∫ x, χ x ^ 2 *
        (f (x + cutoffScale m • EuclideanSpace.single i 1) - f x) ^ 2) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by unfold coordinateDifferenceQuotient; ring
  rw [eLpNorm_eq_ofReal_sqrt_integral_sq hq]
  apply ENNReal.ofReal_le_ofReal
  apply Real.sqrt_le_sqrt
  rw [he]
  calc
    _ ≤ (cutoffScale m)⁻¹ ^ 2 * (M * cutoffScale m ^ 2) :=
      mul_le_mul_of_nonneg_left (henergy m) (sq_nonneg _)
    _ = M := by field_simp [(cutoffScale_pos m).ne']

theorem exists_cutoff_weak_coordinateDerivative_of_difference_energy
    {f χ : Space n → ℝ} (hf : AEStronglyMeasurable f volume) {B : ℝ} (hB : 0 ≤ B)
    (hfB : ∀ᵐ x ∂volume, ‖f x‖ ≤ B) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (i : Fin n) {M : ℝ}
    (henergy : ∀ m, (∫ x, χ x ^ 2 *
      (f (x + cutoffScale m • EuclideanSpace.single i 1) - f x) ^ 2) ≤
      M * cutoffScale m ^ 2) :
    ∃ g : Lp ℝ 2 (volume : Measure (Space n)),
      HasWeakCoordinateDerivative (fun x => χ x * f x) i g :=
  exists_cutoff_weak_coordinateDerivative_of_weighted_difference_bound hf hB hfB hχ hc i
    (eLpNorm_weighted_differenceQuotient_le_of_energy hf hfB hχ.continuous hc i henergy)

end KLS
end
