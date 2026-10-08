import KLS.LocalWeakProduct
import KLS.WeightedFaithfulSmoothing

open MeasureTheory Set Filter Metric
open scoped ContDiff Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The actual coordinate derivative of a locally Lipschitz scalar is its
raw local weak derivative, without a global integrability premise. -/
theorem hasLocalWeakCoordinateDerivative_of_locallyLipschitz
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (i : Fin n) :
    HasLocalWeakCoordinateDerivative f (coordinateDerivative f i) i := by
  intro ψ hψ hψc
  obtain ⟨R, hR⟩ := hψc.isBounded.subset_ball (0 : Space n)
  obtain ⟨L, hL⟩ := hf.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : Space n) R)
  obtain ⟨F, hF, hFeq⟩ := hL.extend_real
  obtain ⟨D, hψLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hψc hψ (by norm_num)
  have hloc (x : Space n) (hx : x ∈ tsupport ψ) : f =ᶠ[𝓝 x] F := by
    filter_upwards [isOpen_ball.mem_nhds (hR hx)] with y hy
    exact hFeq (ball_subset_closedBall hy)
  have hderiv (x : Space n) (hx : x ∈ tsupport ψ) :
      coordinateDerivative F i x = coordinateDerivative f i x := by
    unfold coordinateDerivative
    rw [(hloc x hx).fderiv_eq]
  have heq (x : Space n) (hx : x ∈ tsupport ψ) : F x = f x :=
    (hFeq (ball_subset_closedBall (hR hx))).symm
  have hdψ (x : Space n) (hx : x ∉ tsupport ψ) : coordinateDerivative ψ i x = 0 := by
    simp only [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hx, zero_apply]
  have hid := hF.integral_lineDeriv_mul_eq (μ := (volume : Measure (Space n)))
    hψLip hψc (EuclideanSpace.single i 1)
  have hl : (∫ x, lineDeriv ℝ F x (EuclideanSpace.single i 1) * ψ x) =
      ∫ x, coordinateDerivative f i x * ψ x := by
    apply integral_congr_ae
    filter_upwards [hF.ae_differentiableAt (μ := (volume : Measure (Space n)))] with x hx
    rw [hx.lineDeriv_eq_fderiv]
    change coordinateDerivative F i x * ψ x = _
    by_cases hs : x ∈ tsupport ψ
    · rw [hderiv x hs]
    · rw [image_eq_zero_of_notMem_tsupport hs, mul_zero, mul_zero]
  have hr : (∫ x, lineDeriv ℝ ψ x (-EuclideanSpace.single i 1) * F x) =
      -(∫ x, f x * coordinateDerivative ψ i x) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [((hψ.differentiable (by norm_num)) x).lineDeriv_eq_fderiv, map_neg]
      change -coordinateDerivative ψ i x * F x = _
      by_cases hs : x ∈ tsupport ψ
      · rw [heq x hs]
        ring
      · rw [hdψ x hs]
        ring
  rw [hl, hr] at hid
  linarith

/-- A continuous scalar is essentially bounded on each compact set. -/
theorem memLp_top_restrict_compact_of_continuous
    {f : Space n → ℝ} (hf : Continuous f) {K : Set (Space n)} (hK : IsCompact K) :
    MemLp f ∞ (volume.restrict K) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  apply memLp_top_of_bound hf.measurable.aestronglyMeasurable C
  exact (ae_restrict_iff' hK.measurableSet).mpr (Eventually.of_forall fun x hx => hC x hx)

/-- Actual derivatives of a locally Lipschitz scalar are locally essentially
bounded, including the library's value at nondifferentiability points. -/
theorem memLp_top_coordinateDerivative_of_locallyLipschitz
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (i : Fin n)
    {K : Set (Space n)} (hK : IsCompact K) :
    MemLp (coordinateDerivative f i) ∞ (volume.restrict K) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : Space n)
  obtain ⟨L, hL⟩ := hf.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : Space n) R)
  apply memLp_top_of_bound (measurable_coordinateDerivative f i).aestronglyMeasurable L
  apply (ae_restrict_iff' hK.measurableSet).mpr
  exact Eventually.of_forall fun x hx => by
    have hb : ‖fderiv ℝ f x‖ ≤ L := norm_fderiv_le_of_lipschitzOn ℝ
      (mem_of_superset (isOpen_ball.mem_nhds (hR hx)) ball_subset_closedBall) hL
    calc
      ‖coordinateDerivative f i x‖ ≤ ‖fderiv ℝ f x‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
        (fderiv ℝ f x).le_opNorm _
      _ ≤ L := by simpa using hb

end KLS
end
