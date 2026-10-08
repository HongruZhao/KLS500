import KLS.WeightedCompactSmoothing
import KLS.WeightedEnergyCoercivity

/-! Every faithful locally Lipschitz L² finite-energy test belongs to the actual completed graph. -/

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

lemma continuous_centeredL2_center {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : Continuous (CenteredL2.center μ) := by
  have he : CenteredL2.center μ = fun u : Lp ℝ 2 μ =>
      u - inner ℝ (CenteredL2.oneLp μ) u • CenteredL2.oneLp μ := by
    funext u
    rw [CenteredL2.center, CenteredL2.inner_oneLp]
  rw [he]
  fun_prop

/-- The actual centered value and coordinate derivatives of a faithful finite-energy function. -/
def faithfulCenteredGradientPair {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hf : MemLp f 2 (potentialMeasure φ))
    (hd : ∀ i : Fin n, MemLp (coordinateDerivative f i) 2 (potentialMeasure φ)) :
    WeightedEnergyAmbient φ :=
  WithLp.toLp 2 (Fin.cases (CenteredL2.center (potentialMeasure φ) (hf.toLp f))
    (fun i => (hd i).toLp (coordinateDerivative f i)))

lemma faithfulCenteredGradientPair_value_ae {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hf : MemLp f 2 (potentialMeasure φ))
    (hd : ∀ i : Fin n, MemLp (coordinateDerivative f i) 2 (potentialMeasure φ)) :
    ((faithfulCenteredGradientPair hf hd 0 : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ)
      =ᵐ[potentialMeasure φ] fun x => f x - ∫ y, f y ∂potentialMeasure φ := by
  have hi : (∫ x, (hf.toLp f) x ∂potentialMeasure φ) = ∫ x, f x ∂potentialMeasure φ :=
    integral_congr_ae hf.coeFn_toLp
  filter_upwards [CenteredL2.center_ae (potentialMeasure φ) (hf.toLp f), hf.coeFn_toLp]
    with x hx hy
  change CenteredL2.center (potentialMeasure φ) (hf.toLp f) x = _
  rw [hx, hi, hy]

lemma faithfulCenteredGradientPair_derivative_ae {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hf : MemLp f 2 (potentialMeasure φ))
    (hd : ∀ i : Fin n, MemLp (coordinateDerivative f i) 2 (potentialMeasure φ)) (i : Fin n) :
    ((faithfulCenteredGradientPair hf hd i.succ : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ)
      =ᵐ[potentialMeasure φ] coordinateDerivative f i := (hd i).coeFn_toLp

/-- Strong convergence of actual values and derivatives gives convergence of the centered graph pairs. -/
theorem faithfulCenteredGradientPair_tendsto {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] {f : ℕ → Space n → ℝ} {g : Space n → ℝ}
    (hf : ∀ k, MemLp (f k) 2 (potentialMeasure φ))
    (hfd : ∀ k (i : Fin n), MemLp (coordinateDerivative (f k) i) 2 (potentialMeasure φ))
    (hg : MemLp g 2 (potentialMeasure φ))
    (hgd : ∀ i : Fin n, MemLp (coordinateDerivative g i) 2 (potentialMeasure φ))
    (hconv : Tendsto (fun k => eLpNorm (f k - g) 2 (potentialMeasure φ)) atTop (𝓝 0))
    (hdconv : ∀ i : Fin n, Tendsto (fun k => eLpNorm
      (coordinateDerivative (f k) i - coordinateDerivative g i) 2 (potentialMeasure φ)) atTop (𝓝 0)) :
    Tendsto (fun k => faithfulCenteredGradientPair (hf k) (hfd k))
      atTop (𝓝 (faithfulCenteredGradientPair hg hgd)) := by
  unfold faithfulCenteredGradientPair
  apply (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp
  apply tendsto_pi_nhds.mpr
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact (continuous_centeredL2_center (potentialMeasure φ)).continuousAt.tendsto.comp
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).mpr hconv)
  · exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun k => coordinateDerivative (f k) i) (fun k => hfd k i)
      (coordinateDerivative g i) (hgd i)).mpr (hdconv i)

/-- Compact locally Lipschitz weighted Sobolev functions are in the closure of the genuine smooth core. -/
theorem faithfulCenteredGradientPair_mem_of_compact {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : Continuous φ)
    (hf : LocallyLipschitz f) (hc : HasCompactSupport f)
    (hf2 : MemLp f 2 (potentialMeasure φ))
    (hd2 : ∀ i : Fin n, MemLp (coordinateDerivative f i) 2 (potentialMeasure φ)) :
    faithfulCenteredGradientPair hf2 hd2 ∈ weightedCenteredGradientGraph φ := by
  obtain ⟨hm, hv, hd⟩ := compact_locallyLipschitz_weighted_smoothing hφ hf hc hf2 hd2
  have hpair := faithfulCenteredGradientPair_tendsto
    (fun k => (hm k).2.2.1) (fun k => (hm k).2.2.2) hf2 hd2 hv hd
  have hclosed : IsClosed (weightedCenteredGradientGraph φ : Set (WeightedEnergyAmbient φ)) :=
    Submodule.isClosed_topologicalClosure _
  apply hclosed.mem_of_tendsto hpair
  exact Eventually.of_forall fun k => Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨mollify k f, (hm k).1, (hm k).2.1,
      faithfulCenteredGradientPair_value_ae (hm k).2.2.1 (hm k).2.2.2,
      faithfulCenteredGradientPair_derivative_ae (hm k).2.2.1 (hm k).2.2.2⟩)

/-- The full faithful locally Lipschitz test class of finite energy lies in the actual graph. -/
theorem faithfulCenteredGradientPair_mem {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : Continuous φ)
    (hf : LocallyLipschitzTests (potentialMeasure φ) f)
    (he : energy (potentialMeasure φ) f < ⊤) :
    faithfulCenteredGradientPair hf.2 (memLp_coordinateDerivative_of_energy_lt_top he)
      ∈ weightedCenteredGradientGraph φ := by
  obtain ⟨hc, hv, hd⟩ := faithful_test_compact_cutoff_approximation
    (withDensity_absolutelyContinuous _ _) hf he
  have hpair := faithfulCenteredGradientPair_tendsto
    (fun k => (hc k).2.2.1) (fun k => (hc k).2.2.2) hf.2
    (memLp_coordinateDerivative_of_energy_lt_top he) hv hd
  have hclosed : IsClosed (weightedCenteredGradientGraph φ : Set (WeightedEnergyAmbient φ)) :=
    Submodule.isClosed_topologicalClosure _
  apply hclosed.mem_of_tendsto hpair
  exact Eventually.of_forall fun k => faithfulCenteredGradientPair_mem_of_compact
    hφ (hc k).2.1 (hc k).1 (hc k).2.2.1 (hc k).2.2.2

/-- Every original faithful finite-energy test has its actual centered value and actual derivatives
in the completed weighted graph. No support, smoothness, or decay condition is added to the test. -/
theorem exists_weightedH1_of_faithful_test {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : Continuous φ)
    (hf : LocallyLipschitzTests (potentialMeasure φ) f)
    (he : energy (potentialMeasure φ) f < ⊤) :
    ∃ U : WeightedCenteredH1 φ,
      ((weightedH1Value φ U : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ)
        =ᵐ[potentialMeasure φ] (fun x => f x - ∫ y, f y ∂potentialMeasure φ) ∧
      ∀ i : Fin n,
        ((weightedH1Derivative φ i U : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ)
          =ᵐ[potentialMeasure φ] coordinateDerivative f i := by
  exact ⟨⟨_, faithfulCenteredGradientPair_mem hφ hf he⟩,
    faithfulCenteredGradientPair_value_ae hf.2 (memLp_coordinateDerivative_of_energy_lt_top he),
    faithfulCenteredGradientPair_derivative_ae hf.2 (memLp_coordinateDerivative_of_energy_lt_top he)⟩

/-- Value and energy of the faithful graph representative are exactly the original variance
and extended gradient energy, after their finiteness has been established. -/
theorem weightedH1_faithful_test_norms {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hf : LocallyLipschitzTests (potentialMeasure φ) f)
    (he : energy (potentialMeasure φ) f < ⊤) {U : WeightedCenteredH1 φ}
    (hv : ((weightedH1Value φ U : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ)
      =ᵐ[potentialMeasure φ] fun x => f x - ∫ y, f y ∂potentialMeasure φ)
    (hd : ∀ i : Fin n,
      ((weightedH1Derivative φ i U : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ)
        =ᵐ[potentialMeasure φ] coordinateDerivative f i) :
    ‖weightedH1Value φ U‖ ^ 2 = ProbabilityTheory.variance f (potentialMeasure φ) ∧
    weightedEnergyForm φ U U = (energy (potentialMeasure φ) f).toReal ∧
    variance (potentialMeasure φ) f = ENNReal.ofReal (‖weightedH1Value φ U‖ ^ 2) ∧
    energy (potentialMeasure φ) f = ENNReal.ofReal (weightedEnergyForm φ U U) := by
  have hval : ‖weightedH1Value φ U‖ ^ 2 = ProbabilityTheory.variance f (potentialMeasure φ) := by
    rw [ProbabilityTheory.variance_eq_integral hf.2.aemeasurable,
      ← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    change weightedH1Value φ U x * weightedH1Value φ U x =
      (f x - ∫ y, f y ∂potentialMeasure φ) ^ 2
    rw [hx, pow_two]
  have hderiv (i : Fin n) : (∫ x, weightedH1Derivative φ i U x * weightedH1Derivative φ i U x
      ∂potentialMeasure φ) = ∫ x, coordinateDerivative f i x ^ 2 ∂potentialMeasure φ := by
    apply integral_congr_ae
    filter_upwards [hd i] with x hx
    rw [hx, pow_two]
  have henergy : weightedEnergyForm φ U U = (energy (potentialMeasure φ) f).toReal := by
    rw [weightedEnergyForm_eq_sum_integral, energy_toReal_eq_integral_of_lt_top he]
    simp_rw [hderiv]
    have hgrad : (fun x => ‖gradient f x‖ ^ 2) =
        fun x => ∑ i : Fin n, coordinateDerivative f i x ^ 2 := by
      funext x
      simp_rw [EuclideanSpace.real_norm_sq_eq, coordinateDerivative_eq_gradient]
    rw [hgrad, integral_finsetSum Finset.univ
      (fun i _ => (memLp_coordinateDerivative_of_energy_lt_top he i).integrable_sq)]
  refine ⟨hval, henergy, ?_, ?_⟩
  · rw [hval]
    exact (ENNReal.ofReal_toReal hf.2.evariance_lt_top.ne).symm
  · rw [henergy, ENNReal.ofReal_toReal he.ne]

/-- The completed graph contains every full-class finite-energy test with exact variance and energy. -/
theorem exists_weightedH1_of_faithful_test_with_norms {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : Continuous φ)
    (hf : LocallyLipschitzTests (potentialMeasure φ) f)
    (he : energy (potentialMeasure φ) f < ⊤) :
    ∃ U : WeightedCenteredH1 φ,
      ((weightedH1Value φ U : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ)
        =ᵐ[potentialMeasure φ] (fun x => f x - ∫ y, f y ∂potentialMeasure φ) ∧
      (∀ i : Fin n,
        ((weightedH1Derivative φ i U : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ)
          =ᵐ[potentialMeasure φ] coordinateDerivative f i) ∧
      variance (potentialMeasure φ) f = ENNReal.ofReal (‖weightedH1Value φ U‖ ^ 2) ∧
      energy (potentialMeasure φ) f = ENNReal.ofReal (weightedEnergyForm φ U U) := by
  obtain ⟨U, hv, hd⟩ := exists_weightedH1_of_faithful_test hφ hf he
  have hn := weightedH1_faithful_test_norms hf he hv hd
  exact ⟨U, hv, hd, hn.2.2⟩

end KLS
end

#print axioms KLS.faithfulCenteredGradientPair_mem
#print axioms KLS.exists_weightedH1_of_faithful_test

#print axioms KLS.exists_weightedH1_of_faithful_test_with_norms
