import KLS.WeightedLocalSobolev

/-!
# Strong approximation of actual weak derivatives

The weak integration identity, evaluated on reflected kernels, identifies
the classical derivatives of actual mollifications. Thus the functions and
their weak derivatives converge strongly in L². Compact supports remain
inside one fixed compact enlargement, which permits bounded local weights.
-/

open MeasureTheory InnerProductSpace Set Filter ContinuousLinearMap
open scoped ContDiff ENNReal Convolution Topology Pointwise

noncomputable section
namespace KLS
variable {n : ℕ}

/-- Actual weak differentiation commutes with convolution by a compact C¹ kernel. -/
theorem HasWeakCoordinateDerivative.scalarConvolution_eq {f κ : Space n → ℝ} {i : Fin n}
    {g : Lp ℝ 2 (volume : Measure (Space n))} (hf : MemLp f 2 volume)
    (hg : HasWeakCoordinateDerivative f i g)
    (hκ : ContDiff ℝ 1 κ) (hc : HasCompactSupport κ) (a : Space n) :
    coordinateDerivative (scalarConvolution f κ) i a = scalarConvolution g κ a := by
  rw [coordinateDerivative_scalarConvolution (hf.locallyIntegrable (by norm_num)) hκ hc]
  have ht : ContDiff ℝ 1 (fun y => κ (a - y)) :=
    hκ.comp (contDiff_const.sub contDiff_id)
  have htc : HasCompactSupport (fun y => κ (a - y)) :=
    hc.comp_homeomorph (Homeomorph.subLeft a)
  have he := hg (fun y => κ (a - y)) ht htc
  have hl : (∫ y, f y * coordinateDerivative (fun z => κ (a - z)) i y) =
      -(scalarConvolution f (coordinateDerivative κ i) a) := by
    unfold scalarConvolution
    rw [convolution_def, ← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only
      rw [coordinateDerivative_const_sub (hκ.differentiable (by norm_num))]
      simp
  rw [hl] at he
  exact neg_injective he

/-- The actual derivative of each mollification equals the mollified weak derivative. -/
theorem HasWeakCoordinateDerivative.mollify_eq {f : Space n → ℝ} {i : Fin n}
    {g : Lp ℝ 2 (volume : Measure (Space n))} (hf : MemLp f 2 volume)
    (hg : HasWeakCoordinateDerivative f i g) (k : ℕ) :
    coordinateDerivative (mollify k f) i = mollify k g := by
  funext x
  exact hg.scalarConvolution_eq hf ((mollifierKernel_contDiff k).of_le (by simp))
    (mollifierKernel_hasCompactSupport k) x

/-- Strong L² convergence holds for the actual classical coordinate derivatives. -/
theorem HasWeakCoordinateDerivative.eLpNorm_mollify_derivative_sub_tendsto_zero
    {f : Space n → ℝ} {i : Fin n} {g : Lp ℝ 2 (volume : Measure (Space n))}
    (hf : MemLp f 2 volume) (hg : HasWeakCoordinateDerivative f i g) :
    Tendsto (fun k => eLpNorm (coordinateDerivative (mollify k f) i - (g : Space n → ℝ)) 2 volume)
      atTop (𝓝 0) := by
  simpa only [hg.mollify_eq hf] using eLpNorm_mollify_sub_tendsto_zero (Lp.memLp g)

theorem hasCompactSupport_mollify {f : Space n → ℝ} (hc : HasCompactSupport f) (k : ℕ) :
    HasCompactSupport (mollify k f) :=
  HasCompactSupport.convolution (lsmul ℝ ℝ) hc (mollifierKernel_hasCompactSupport k)

/-- All approximating supports lie in one actual compact set. -/
theorem tsupport_mollify_subset {f : Space n → ℝ} (hc : HasCompactSupport f) (k : ℕ) :
    tsupport (mollify k f) ⊆ mollifierEnlargement (tsupport f) := by
  apply closure_minimal
  · exact (support_convolution_subset (lsmul ℝ ℝ)).trans
      (Set.add_subset_add (subset_tsupport f) (mollifierKernel_support_subset k))
  · exact (isCompact_mollifierEnlargement hc).isClosed

/-- Strong L² approximation passes through an actual L² integral pairing. -/
theorem tendsto_integral_mul_of_eLpNorm_sub_tendsto_zero
    {f : ℕ → Space n → ℝ} {u b : Space n → ℝ}
    (hf : ∀ k, MemLp (f k) 2 volume) (hu : MemLp u 2 volume) (hb : MemLp b 2 volume)
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, b x * f k x) atTop (𝓝 (∫ x, b x * u x)) := by
  have ht := tendsto_toLp_of_eLpNorm_sub_tendsto_zero hf hu hconv
  have hcont : Continuous (fun v : Lp ℝ 2 (volume : Measure (Space n)) =>
      inner ℝ (hb.toLp b) v) := continuous_const.inner continuous_id
  have hi := hcont.continuousAt.tendsto.comp ht
  convert hi using 1
  · funext k
    dsimp only [Function.comp_def]
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hb.coeFn_toLp, (hf k).coeFn_toLp] with x hx hy
    simp [hx, hy, mul_comm]
  · rw [L2.inner_def]
    congr 1
    apply integral_congr_ae
    filter_upwards [hb.coeFn_toLp, hu.coeFn_toLp] with x hx hy
    simp [hx, hy, mul_comm]

end KLS
end

#print axioms KLS.HasWeakCoordinateDerivative.scalarConvolution_eq
#print axioms KLS.HasWeakCoordinateDerivative.eLpNorm_mollify_derivative_sub_tendsto_zero
#print axioms KLS.tsupport_mollify_subset
#print axioms KLS.tendsto_integral_mul_of_eLpNorm_sub_tendsto_zero
