import KLS.WeightedEnergyGraphCore
import KLS.WeightedCompactL2Maps
import EllipticPdes.Analysis.FrechetKolmogorov
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! Local compactness of the actual weighted value embedding from actual translations. -/
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff RealInnerProductSpace Topology
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The smooth translation estimate applied to actual L² representatives and derivative coordinates. -/
theorem compact_translation_bound_of_smooth {F : Space n → ℝ}
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F)
    (u : Lp ℝ 2 (volume : Measure (Space n)))
    (D : Fin n → Lp ℝ 2 (volume : Measure (Space n)))
    (hu : (u : Space n → ℝ) =ᵐ[volume] F)
    (hD : ∀ i, (D i : Space n → ℝ) =ᵐ[volume] coordinateDerivative F i)
    (h : Space n) :
    ‖transL2 h u - u‖ ≤ (∑ i : Fin n, ‖D i‖) * ‖h‖ := by
  have hsum : 0 ≤ ∑ i : Fin n, ‖D i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  apply le_of_sq_le_sq _ (mul_nonneg hsum (norm_nonneg _))
  rw [norm_sq_transL2_sub]
  have htrans : (fun x => (u (x + h) - u x) ^ 2) =ᵐ[volume]
      fun x => (F (x + h) - F x) ^ 2 := by
    filter_upwards [(measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp hu,
      hu] with x hx hy
    dsimp only [Function.comp_def] at hx
    rw [hx, hy]
  rw [integral_congr_ae htrans]
  have hnorm (x : Space n) : ‖fderiv ℝ F x‖ ^ 2 =
      ∑ i : Fin n, (coordinateDerivative F i x) ^ 2 := by
    rw [← toDual_gradient]
    simp_rw [(toDual ℝ (Space n)).norm_map, EuclideanSpace.real_norm_sq_eq,
      ← coordinateDerivative_eq_gradient]
  have hi (i : Fin n) : Integrable (fun x => (coordinateDerivative F i x) ^ 2) volume :=
    ((memLp_congr_ae (hD i)).mp (Lp.memLp (D i))).integrable_sq
  have hd (i : Fin n) : (∫ x, (coordinateDerivative F i x) ^ 2) = ‖D i‖ ^ 2 := by
    rw [MeasureTheory.norm_sq_eq_integral_sq]
    apply integral_congr_ae
    filter_upwards [hD i] with x hx
    rw [hx]
  have he : (∫ x, ‖fderiv ℝ F x‖ ^ 2) = ∑ i : Fin n, ‖D i‖ ^ 2 := by
    simp_rw [hnorm]
    rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
    simp_rw [hd]
  have hb := integral_sq_sub_translation_le hF hc h
  rw [he] at hb
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (fun i _ => norm_nonneg (D i))
  calc
    _ ≤ ‖h‖ ^ 2 * ∑ i : Fin n, ‖D i‖ ^ 2 := hb
    _ ≤ ‖h‖ ^ 2 * (∑ i : Fin n, ‖D i‖) ^ 2 := mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = _ := by ring

private def ambientCompactValue {φ χ : Space n → ℝ}
    (hφ : Continuous φ) (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    WeightedEnergyAmbient φ →L[ℝ] Lp ℝ 2 (volume : Measure (Space n)) :=
  (weightedL2CompactToVolume hφ hχ hc).comp
    (PiLp.proj 2 (fun _ : Fin (n + 1) => Lp ℝ 2 (potentialMeasure φ)) 0)

private def ambientCompactDerivative {φ χ : Space n → ℝ}
    (hφ : Continuous φ) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (i : Fin n) :
    WeightedEnergyAmbient φ →L[ℝ] Lp ℝ 2 (volume : Measure (Space n)) :=
  (weightedL2CompactToVolume hφ hχ.continuous hc).comp
    (PiLp.proj 2 (fun _ : Fin (n + 1) => Lp ℝ 2 (potentialMeasure φ)) i.succ) +
  (weightedL2CompactToVolume hφ
    (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous
    (hasCompactSupport_coordinateDerivative hc i)).comp
    (PiLp.proj 2 (fun _ : Fin (n + 1) => Lp ℝ 2 (potentialMeasure φ)) 0)

private theorem ambientCompactDerivative_coe {φ χ : Space n → ℝ}
    (hφ : Continuous φ) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (i : Fin n) (W : WeightedEnergyAmbient φ) :
    ambientCompactDerivative hφ hχ hc i W =ᵐ[volume] fun x =>
      χ x * W i.succ x + coordinateDerivative χ i x * W 0 x := by
  let T := weightedL2CompactToVolume hφ
    (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous
    (hasCompactSupport_coordinateDerivative hc i)
  filter_upwards [weightedL2CompactToVolume_coe hφ hχ.continuous hc (W i.succ),
    weightedL2CompactToVolume_coe hφ
      (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous
      (hasCompactSupport_coordinateDerivative hc i) (W 0),
    Lp.coeFn_add (weightedL2CompactToVolume hφ hχ.continuous hc (W i.succ)) (T (W 0))]
    with x hx hy hz
  change (weightedL2CompactToVolume hφ hχ.continuous hc (W i.succ) + T (W 0)) x = _
  rw [hz, Pi.add_apply, hx, hy]

private theorem core_compact_translation_bound {φ χ : Space n → ℝ}
    (hφ : Continuous φ) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    {W : WeightedEnergyAmbient φ} (hW : W ∈ smoothCenteredGradientGraphSet φ) (h : Space n) :
    ‖transL2 h (ambientCompactValue hφ hχ.continuous hc W) -
        ambientCompactValue hφ hχ.continuous hc W‖ ≤
      (∑ i : Fin n, ‖ambientCompactDerivative hφ hχ hc i W‖) * ‖h‖ := by
  obtain ⟨f, hf, _, hv, hd⟩ := hW
  let f₀ : Space n → ℝ := fun x => f x - ∫ y, f y ∂potentialMeasure φ
  have hf₀ : ContDiff ℝ 1 f₀ := (hf.of_le (by norm_num)).sub contDiff_const
  have hd₀ (i : Fin n) : coordinateDerivative f₀ i = coordinateDerivative f i := by
    funext x
    unfold coordinateDerivative
    dsimp [f₀]
    rw [fderiv_fun_sub (hf.differentiable (by norm_num) x) (differentiableAt_const _)]
    simp
  apply compact_translation_bound_of_smooth (F := fun x => χ x * f₀ x)
    (hχ.mul hf₀) hc.mul_right
  · filter_upwards [weightedL2CompactToVolume_coe hφ hχ.continuous hc (W 0),
      (volume_absolutelyContinuous_potentialMeasure hφ).ae_eq hv] with x hx hy
    change weightedL2CompactToVolume hφ hχ.continuous hc (W 0) x = _
    rw [hx, hy]
  · intro i
    filter_upwards [ambientCompactDerivative_coe hφ hχ hc i W,
      (volume_absolutelyContinuous_potentialMeasure hφ).ae_eq hv,
      (volume_absolutelyContinuous_potentialMeasure hφ).ae_eq (hd i)] with x hx hy hz
    rw [hx, hy, hz, coordinateDerivative_mul (hχ.differentiable (by norm_num) x)
      (hf₀.differentiable (by norm_num) x), hd₀]
    dsimp [f₀]
    ring

/-- The actual compact localization has a translation modulus controlled by its actual derivatives. -/
theorem weightedH1CompactValue_translation_bound {φ χ : Space n → ℝ}
    (hφ : Continuous φ) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (U : WeightedCenteredH1 φ) (h : Space n) :
    ‖transL2 h (weightedH1CompactValue hφ hχ.continuous hc U) -
        weightedH1CompactValue hφ hχ.continuous hc U‖ ≤
      (∑ i : Fin n, ‖weightedH1CompactDerivative hφ hχ hc i U‖) * ‖h‖ := by
  have hclosed : IsClosed {W : WeightedEnergyAmbient φ |
      ‖transL2 h (ambientCompactValue hφ hχ.continuous hc W) -
          ambientCompactValue hφ hχ.continuous hc W‖ ≤
        (∑ i : Fin n, ‖ambientCompactDerivative hφ hχ hc i W‖) * ‖h‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hcore : smoothCenteredGradientGraphSet φ ⊆ {W : WeightedEnergyAmbient φ |
      ‖transL2 h (ambientCompactValue hφ hχ.continuous hc W) -
          ambientCompactValue hφ hχ.continuous hc W‖ ≤
        (∑ i : Fin n, ‖ambientCompactDerivative hφ hχ hc i W‖) * ‖h‖} :=
    fun _ hW => core_compact_translation_bound hφ hχ hc hW h
  have hU : (U : WeightedEnergyAmbient φ) ∈ closure (smoothCenteredGradientGraphSet φ) := by
    rw [← weightedCenteredGradientGraph_coe_eq_closure hφ]
    exact U.property
  exact (closure_minimal hcore hclosed) hU


/-- The actual compactly localized image of the energy unit ball is totally bounded in volume L². -/
theorem weightedH1CompactValue_totallyBounded {φ χ : Space n → ℝ}
    (hφ : Continuous φ) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    TotallyBounded ((weightedH1CompactValue hφ hχ.continuous hc) ''
      closedBall (0 : WeightedCenteredH1 φ) 1) := by
  let T := weightedH1CompactValue hφ hχ.continuous hc
  let D := weightedH1CompactDerivative hφ hχ hc
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : Space n)
  apply EllipticPdes.Analysis.totallyBounded_of_lipschitz_translation
    (R := R) (M := ‖T‖) (Λ := ∑ i : Fin n, ‖D i‖)
  · rintro v ⟨U, hU, rfl⟩
    have hUn : ‖U‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hU
    exact (T.le_opNorm U).trans (by
      simpa only [mul_one] using (mul_le_mul_of_nonneg_left hUn (norm_nonneg T)))
  · rintro v ⟨U, _, rfl⟩
    filter_upwards [weightedH1CompactValue_coe hφ hχ.continuous hc U] with x hx
    intro hxR
    rw [hx]
    have hxout : x ∉ tsupport χ := fun hxs => hxR (hR hxs)
    rw [image_eq_zero_of_notMem_tsupport hxout, zero_mul]
  · rintro v ⟨U, hU, rfl⟩ h
    have hUn : ‖U‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hU
    have hd (i : Fin n) : ‖D i U‖ ≤ ‖D i‖ :=
      ((D i).le_opNorm U).trans (by
        simpa only [mul_one] using (mul_le_mul_of_nonneg_left hUn (norm_nonneg (D i))))
    exact (weightedH1CompactValue_translation_bound hφ hχ hc U h).trans
      (mul_le_mul_of_nonneg_right (Finset.sum_le_sum (fun i _ => hd i)) (norm_nonneg h))

/-- Every actual compact C¹ localization of the weighted value embedding is a compact operator. -/
theorem weightedH1CompactValue_isCompactOperator {φ χ : Space n → ℝ}
    (hφ : Continuous φ) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    IsCompactOperator (weightedH1CompactValue hφ hχ.continuous hc) := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall
    (weightedH1CompactValue hφ hχ.continuous hc).toLinearMap zero_lt_one).mpr
  exact (weightedH1CompactValue_totallyBounded hφ hχ hc).closure.isCompact_of_isClosed isClosed_closure

end KLS
end
#print axioms KLS.compact_translation_bound_of_smooth
#print axioms KLS.weightedH1CompactValue_translation_bound

#print axioms KLS.weightedH1CompactValue_totallyBounded
#print axioms KLS.weightedH1CompactValue_isCompactOperator
