import KLS.WeightedEnergyGraphClosability

/-! Compact continuous multiplication transports actual weighted and Lebesgue L² classes. -/
open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff RealInnerProductSpace
noncomputable section
namespace KLS
variable {n : ℕ}

private theorem compactSquareWeight_bound {φ χ : Space n → ℝ}
    (hφ : Continuous φ) (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖χ x ^ 2 * Real.exp (φ x)‖ ≤ B := by
  have hc2 : HasCompactSupport (fun x => χ x ^ 2) := by
    have ht := (hc.mul_right : HasCompactSupport (χ * χ))
    change HasCompactSupport (fun x => χ x * χ x) at ht
    simpa only [pow_two] using ht
  obtain ⟨B, hB⟩ := (hc2.mul_right : HasCompactSupport
      (fun x => χ x ^ 2 * Real.exp (φ x))).exists_bound_of_continuous
        ((hχ.pow 2).mul (Real.continuous_exp.comp hφ))
  exact ⟨B, (norm_nonneg _).trans (hB 0), hB⟩

private theorem square_weight_cancellation (a b t : ℝ) :
    (a ^ 2 * Real.exp t * b ^ 2) * Real.exp (-t) = (a * b) ^ 2 := by
  calc
    _ = (a * b) ^ 2 * (Real.exp t * Real.exp (-t)) := by ring
    _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- A compact continuous multiplier sends a weighted L² representative into Lebesgue L². -/
theorem memLp_compact_mul_weighted_to_volume {φ χ : Space n → ℝ}
    (hφ : Continuous φ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (u : Lp ℝ 2 (potentialMeasure φ)) : MemLp (fun x => χ x * u x) 2 volume := by
  obtain ⟨B, _, hB⟩ := compactSquareWeight_bound hφ hχ hc
  have hi : Integrable (fun x => (χ x ^ 2 * Real.exp (φ x)) * u x ^ 2)
      (potentialMeasure φ) :=
    (Lp.memLp u).integrable_sq.bdd_mul ((hχ.pow 2).mul (Real.continuous_exp.comp hφ)).aestronglyMeasurable
      (Eventually.of_forall hB)
  have hi' := (integrable_potentialMeasure_iff hφ.measurable).mp hi
  have hm : AEStronglyMeasurable (fun x => χ x * u x) volume :=
    hχ.aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable u).mono_ac (volume_absolutelyContinuous_potentialMeasure hφ))
  apply (memLp_two_iff_integrable_sq hm).mpr
  convert hi' using 1
  funext x
  exact (square_weight_cancellation (χ x) (u x) (φ x)).symm

/-- The local transport has a finite operator bound derived from the actual compact multiplier. -/
theorem exists_compact_mul_weighted_to_volume_bound {φ χ : Space n → ℝ}
    (hφ : Continuous φ) (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Lp ℝ 2 (potentialMeasure φ),
      ‖(memLp_compact_mul_weighted_to_volume hφ hχ hc u).toLp (fun x => χ x * u x)‖ ≤ C * ‖u‖ := by
  obtain ⟨B, hB, hbound⟩ := compactSquareWeight_bound hφ hχ hc
  refine ⟨B + 1, by positivity, ?_⟩
  intro u
  let v := (memLp_compact_mul_weighted_to_volume hφ hχ hc u).toLp (fun x => χ x * u x)
  have hi : Integrable (fun x => (χ x ^ 2 * Real.exp (φ x)) * u x ^ 2)
      (potentialMeasure φ) :=
    (Lp.memLp u).integrable_sq.bdd_mul ((hχ.pow 2).mul (Real.continuous_exp.comp hφ)).aestronglyMeasurable
      (Eventually.of_forall hbound)
  have hn : ‖v‖ ^ 2 = ∫ x, (χ x ^ 2 * Real.exp (φ x)) * u x ^ 2 ∂potentialMeasure φ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def, integral_potentialMeasure hφ.measurable]
    apply integral_congr_ae
    filter_upwards [(memLp_compact_mul_weighted_to_volume hφ hχ hc u).coeFn_toLp] with x hx
    change inner ℝ (v x) (v x) = _
    rw [show v x = χ x * u x from hx, square_weight_cancellation]
    simp only [RCLike.inner_apply, conj_trivial, pow_two]
  have hun : ‖u‖ ^ 2 = ∫ x, u x ^ 2 ∂potentialMeasure φ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    congr 1
    funext x
    simp only [RCLike.inner_apply, conj_trivial, pow_two]
  have hb := integral_mono hi ((Lp.memLp u).integrable_sq.const_mul B) (fun x =>
    mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hbound x)) (sq_nonneg (u x)))
  rw [integral_const_mul, ← hun, ← hn] at hb
  have hnon : 0 ≤ (B + 1) * ‖u‖ := by positivity
  have hsq : B ≤ (B + 1) ^ 2 := by nlinarith
  have hs := mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖u‖)
  change ‖v‖ ≤ (B + 1) * ‖u‖
  nlinarith [norm_nonneg v]

/-- Compact continuous multiplication also sends Lebesgue L² into the actual weighted L². -/
theorem memLp_compact_mul_volume_to_weighted {φ χ : Space n → ℝ}
    (hφ : Continuous φ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (u : Lp ℝ 2 (volume : Measure (Space n))) :
    MemLp (fun x => χ x * u x) 2 (potentialMeasure φ) := by
  obtain ⟨B, _, hB⟩ := compactSquareWeight_bound hφ.neg hχ hc
  have hi : Integrable (fun x => (χ x ^ 2 * Real.exp (-φ x)) * u x ^ 2) volume :=
    (Lp.memLp u).integrable_sq.bdd_mul ((hχ.pow 2).mul (Real.continuous_exp.comp hφ.neg)).aestronglyMeasurable
      (Eventually.of_forall hB)
  have hm : AEStronglyMeasurable (fun x => χ x * u x) (potentialMeasure φ) :=
    hχ.aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable u).mono_ac (withDensity_absolutelyContinuous _ _))
  apply (memLp_two_iff_integrable_sq hm).mpr
  rw [integrable_potentialMeasure_iff hφ.measurable]
  convert hi using 1
  funext x
  ring

/-- The reverse local transport has a finite operator bound from the actual compact multiplier. -/
theorem exists_compact_mul_volume_to_weighted_bound {φ χ : Space n → ℝ}
    (hφ : Continuous φ) (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Lp ℝ 2 (volume : Measure (Space n)),
      ‖(memLp_compact_mul_volume_to_weighted hφ hχ hc u).toLp (fun x => χ x * u x)‖ ≤ C * ‖u‖ := by
  obtain ⟨B, hB, hbound⟩ := compactSquareWeight_bound hφ.neg hχ hc
  refine ⟨B + 1, by positivity, ?_⟩
  intro u
  let v := (memLp_compact_mul_volume_to_weighted hφ hχ hc u).toLp (fun x => χ x * u x)
  have hi : Integrable (fun x => (χ x ^ 2 * Real.exp (-φ x)) * u x ^ 2) volume :=
    (Lp.memLp u).integrable_sq.bdd_mul ((hχ.pow 2).mul (Real.continuous_exp.comp hφ.neg)).aestronglyMeasurable
      (Eventually.of_forall hbound)
  have hn : ‖v‖ ^ 2 = ∫ x, (χ x ^ 2 * Real.exp (-φ x)) * u x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    have he : (∫ x, inner ℝ (v x) (v x) ∂potentialMeasure φ) =
        ∫ x, (χ x * u x) ^ 2 ∂potentialMeasure φ := by
      apply integral_congr_ae
      filter_upwards [(memLp_compact_mul_volume_to_weighted hφ hχ hc u).coeFn_toLp] with x hx
      rw [show v x = χ x * u x from hx]
      simp only [RCLike.inner_apply, conj_trivial, pow_two]
    rw [he, integral_potentialMeasure hφ.measurable]
    congr 1
    funext x
    ring
  have hun : ‖u‖ ^ 2 = ∫ x, u x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    congr 1
    funext x
    simp only [RCLike.inner_apply, conj_trivial, pow_two]
  have hb := integral_mono hi ((Lp.memLp u).integrable_sq.const_mul B) (fun x =>
    mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hbound x)) (sq_nonneg (u x)))
  rw [integral_const_mul, ← hun, ← hn] at hb
  have hnon : 0 ≤ (B + 1) * ‖u‖ := by positivity
  have hsq : B ≤ (B + 1) ^ 2 := by nlinarith
  have hs := mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖u‖)
  change ‖v‖ ≤ (B + 1) * ‖u‖
  nlinarith [norm_nonneg v]


private def l2CompactMulLinear (μ ν : Measure (Space n)) (χ : Space n → ℝ)
    (hνμ : ν ≪ μ) (hm : ∀ u : Lp ℝ 2 μ, MemLp (fun x => χ x * u x) 2 ν) :
    Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 ν where
  toFun u := (hm u).toLp (fun x => χ x * u x)
  map_add' := by
    intro u v
    apply Lp.ext
    filter_upwards [(hm (u + v)).coeFn_toLp, (hm u).coeFn_toLp, (hm v).coeFn_toLp,
      hνμ.ae_eq (Lp.coeFn_add u v), Lp.coeFn_add ((hm u).toLp _) ((hm v).toLp _)]
      with x ha hu hv huv ha'
    rw [ha, ha', Pi.add_apply, hu, hv, huv, Pi.add_apply]
    ring
  map_smul' := by
    intro c u
    apply Lp.ext
    filter_upwards [(hm (c • u)).coeFn_toLp, (hm u).coeFn_toLp,
      hνμ.ae_eq (Lp.coeFn_smul c u), Lp.coeFn_smul c ((hm u).toLp _)]
      with x ha hu hcu ha'
    simp only [RingHom.id_apply]
    rw [ha, ha', Pi.smul_apply, hu, hcu, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring

/-- The actual bounded linear map `u ↦ χu` from weighted L² to Lebesgue L². -/
def weightedL2CompactToVolume {φ χ : Space n → ℝ}
    (hφ : Continuous φ) (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    Lp ℝ 2 (potentialMeasure φ) →L[ℝ] Lp ℝ 2 (volume : Measure (Space n)) :=
  let hb := exists_compact_mul_weighted_to_volume_bound hφ hχ hc
  (l2CompactMulLinear (potentialMeasure φ) volume χ
    (volume_absolutelyContinuous_potentialMeasure hφ)
    (memLp_compact_mul_weighted_to_volume hφ hχ hc)).mkContinuous hb.choose
      (by intro u; exact hb.choose_spec.2 u)

theorem weightedL2CompactToVolume_coe {φ χ : Space n → ℝ}
    (hφ : Continuous φ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (u : Lp ℝ 2 (potentialMeasure φ)) :
    weightedL2CompactToVolume hφ hχ hc u =ᵐ[volume] fun x => χ x * u x :=
  (memLp_compact_mul_weighted_to_volume hφ hχ hc u).coeFn_toLp

/-- The actual bounded linear map `u ↦ χu` from Lebesgue L² to weighted L². -/
def volumeL2CompactToWeighted {φ χ : Space n → ℝ}
    (hφ : Continuous φ) (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    Lp ℝ 2 (volume : Measure (Space n)) →L[ℝ] Lp ℝ 2 (potentialMeasure φ) :=
  let hb := exists_compact_mul_volume_to_weighted_bound hφ hχ hc
  (l2CompactMulLinear volume (potentialMeasure φ) χ
    (withDensity_absolutelyContinuous _ _)
    (memLp_compact_mul_volume_to_weighted hφ hχ hc)).mkContinuous hb.choose
      (by intro u; exact hb.choose_spec.2 u)

theorem volumeL2CompactToWeighted_coe {φ χ : Space n → ℝ}
    (hφ : Continuous φ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (u : Lp ℝ 2 (volume : Measure (Space n))) :
    volumeL2CompactToWeighted hφ hχ hc u =ᵐ[potentialMeasure φ] fun x => χ x * u x :=
  (memLp_compact_mul_volume_to_weighted hφ hχ hc u).coeFn_toLp

/-- Composing the two genuine transport maps multiplies a weighted representative by `χ²`. -/
theorem volumeL2CompactToWeighted_comp_coe {φ χ : Space n → ℝ}
    (hφ : Continuous φ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (u : Lp ℝ 2 (potentialMeasure φ)) :
    volumeL2CompactToWeighted hφ hχ hc (weightedL2CompactToVolume hφ hχ hc u)
      =ᵐ[potentialMeasure φ] fun x => χ x ^ 2 * u x := by
  have hac : potentialMeasure φ ≪ volume := withDensity_absolutelyContinuous _ _
  filter_upwards [volumeL2CompactToWeighted_coe hφ hχ hc (weightedL2CompactToVolume hφ hχ hc u),
    hac.ae_eq (weightedL2CompactToVolume_coe hφ hχ hc u)] with x hx hy
  rw [hx, hy]
  ring

/-- Compact localization of an actual energy-graph value, as a continuous map into Lebesgue L². -/
def weightedH1CompactValue {φ χ : Space n → ℝ}
    (hφ : Continuous φ) (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    WeightedCenteredH1 φ →L[ℝ] Lp ℝ 2 (volume : Measure (Space n)) :=
  (weightedL2CompactToVolume hφ hχ hc).comp (weightedH1Value φ)

/-- The actual product-rule derivative of compact localization, also a bounded linear map. -/
def weightedH1CompactDerivative {φ χ : Space n → ℝ}
    (hφ : Continuous φ) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (i : Fin n) :
    WeightedCenteredH1 φ →L[ℝ] Lp ℝ 2 (volume : Measure (Space n)) :=
  (weightedL2CompactToVolume hφ hχ.continuous hc).comp (weightedH1Derivative φ i) +
  (weightedL2CompactToVolume hφ
    (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous
    (hasCompactSupport_coordinateDerivative hc i)).comp (weightedH1Value φ)

theorem weightedH1CompactValue_coe {φ χ : Space n → ℝ}
    (hφ : Continuous φ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (U : WeightedCenteredH1 φ) :
    weightedH1CompactValue hφ hχ hc U =ᵐ[volume] fun x => χ x * weightedH1Value φ U x :=
  weightedL2CompactToVolume_coe hφ hχ hc (weightedH1Value φ U)

theorem weightedH1CompactDerivative_coe {φ χ : Space n → ℝ}
    (hφ : Continuous φ) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (i : Fin n) (U : WeightedCenteredH1 φ) :
    weightedH1CompactDerivative hφ hχ hc i U =ᵐ[volume] fun x =>
      χ x * weightedH1Derivative φ i U x + coordinateDerivative χ i x * weightedH1Value φ U x := by
  let T := weightedL2CompactToVolume hφ
    (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous
    (hasCompactSupport_coordinateDerivative hc i)
  filter_upwards [weightedL2CompactToVolume_coe hφ hχ.continuous hc (weightedH1Derivative φ i U),
    weightedL2CompactToVolume_coe hφ
      (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous
      (hasCompactSupport_coordinateDerivative hc i) (weightedH1Value φ U),
    Lp.coeFn_add (weightedL2CompactToVolume hφ hχ.continuous hc (weightedH1Derivative φ i U))
      (T (weightedH1Value φ U))] with x hx hy hz
  change (weightedL2CompactToVolume hφ hχ.continuous hc (weightedH1Derivative φ i U) +
    T (weightedH1Value φ U)) x = _
  rw [hz, Pi.add_apply, hx, hy]

/-- The continuous localized derivative is the actual weak derivative, not an independent coordinate. -/
theorem weightedH1CompactDerivative_hasWeakCoordinateDerivative {φ χ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (i : Fin n) (U : WeightedCenteredH1 φ) :
    HasWeakCoordinateDerivative (fun x => χ x * weightedH1Value φ U x) i
      (weightedH1CompactDerivative hφ.continuous hχ hc i U) := by
  obtain ⟨_, g, hg, hw⟩ := weightedH1_compact_mul_hasWeakCoordinateDerivative hφ U hχ hc i
  have heq : g = weightedH1CompactDerivative hφ.continuous hχ hc i U := by
    apply Lp.ext
    exact hg.trans (weightedH1CompactDerivative_coe hφ.continuous hχ hc i U).symm
  rwa [heq] at hw

end KLS
end
#print axioms KLS.memLp_compact_mul_weighted_to_volume
#print axioms KLS.exists_compact_mul_weighted_to_volume_bound
#print axioms KLS.memLp_compact_mul_volume_to_weighted
#print axioms KLS.exists_compact_mul_volume_to_weighted_bound

#print axioms KLS.weightedL2CompactToVolume
#print axioms KLS.volumeL2CompactToWeighted
#print axioms KLS.weightedH1CompactDerivative_hasWeakCoordinateDerivative
