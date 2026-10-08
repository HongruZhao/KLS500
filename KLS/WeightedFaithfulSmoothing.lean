import KLS.WeightedFaithfulCutoff
import KLS.WeakDerivativeMollification

/-! Actual weak derivatives and compact smoothing for faithful locally Lipschitz tests. -/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology ContDiff ENNReal

noncomputable section
namespace KLS
variable {n : ℕ}

/-- Locally Lipschitz functions have their actual coordinate derivatives as weak derivatives.
The proof localizes each test inside a ball and applies the library's Lipschitz integration by parts. -/
theorem locallyLipschitz_hasWeakCoordinateDerivative {f : Space n → ℝ}
    (hf : LocallyLipschitz f) (i : Fin n) {g : Lp ℝ 2 (volume : Measure (Space n))}
    (hg : (g : Space n → ℝ) =ᵐ[volume] coordinateDerivative f i) :
    HasWeakCoordinateDerivative f i g := by
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
  have hgI : (∫ x, g x * ψ x) = ∫ x, coordinateDerivative f i x * ψ x :=
    integral_congr_ae (hg.fun_mul (EventuallyEq.rfl))
  rw [hgI]
  linarith

/-- For every actual locally Lipschitz Sobolev function, derivatives of its smooth
mollifications converge strongly to the actual derivatives. -/
theorem eLpNorm_mollify_coordinateDerivative_sub_tendsto_zero
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (hf2 : MemLp f 2 volume)
    (i : Fin n) (hd2 : MemLp (coordinateDerivative f i) 2 volume) :
    Tendsto (fun k => eLpNorm
      (coordinateDerivative (mollify k f) i - coordinateDerivative f i) 2 volume)
      atTop (𝓝 0) := by
  let g : Lp ℝ 2 volume := hd2.toLp (coordinateDerivative f i)
  have hg : (g : Space n → ℝ) =ᵐ[volume] coordinateDerivative f i := hd2.coeFn_toLp
  have hw := locallyLipschitz_hasWeakCoordinateDerivative hf i hg
  have ht := hw.eLpNorm_mollify_derivative_sub_tendsto_zero hf2
  have he (k : ℕ) : eLpNorm (coordinateDerivative (mollify k f) i - (g : Space n → ℝ)) 2 volume =
      eLpNorm (coordinateDerivative (mollify k f) i - coordinateDerivative f i) 2 volume :=
    eLpNorm_congr_ae (EventuallyEq.rfl.sub hg)
  simpa only [he] using ht

end KLS
end

#print axioms KLS.locallyLipschitz_hasWeakCoordinateDerivative
#print axioms KLS.eLpNorm_mollify_coordinateDerivative_sub_tendsto_zero
