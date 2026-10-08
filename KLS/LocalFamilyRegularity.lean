import KLS.LocalFamilyPath

/-! Adaptedness, continuity before the lifetime, and genuine finite-lifetime escape. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace KLS.LocalDiffusion.LocalProcessFamily
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {N d : ℕ} {W : MultidimBrownianMotion P d} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
  {b : (Fin N → ℝ) → Fin N → ℝ} {s : Fin d → (Fin N → ℝ) → Fin N → ℝ}
  (D : LocalProcessFamily W ℱ hW b s)

theorem measurable_path_slice (t : ℝ) : Measurable[ℱ t] (D.path t) :=
  @Measurable.of_eval Ω (Fin N) (fun _ => ℝ) (ℱ t) (fun _ => inferInstance) (D.path t)
    (fun i => ((D.progressive_path i).stronglyMeasurable_eval t).measurable)

/-- The assembled path is continuous on its nonnegative interval of existence. -/
theorem ae_continuousOn_before_lifetime : ∀ᵐ ω ∂P,
    ContinuousOn (fun t => D.path t ω) {t : ℝ | 0 ≤ t ∧ (t : WithTop ℝ) < D.lifetime ω} := by
  filter_upwards [D.ae_path_eq_of_lt_exit] with ω hp
  intro t ht
  obtain ⟨m, hm⟩ := (D.lt_lifetime_iff ω t).mp ht.2
  have hU : {u : ℝ | (u : WithTop ℝ) < D.exit m ω} ∈ 𝓝 t :=
    (isOpen_lt WithTop.continuous_coe continuous_const).mem_nhds hm
  have heq : (fun u => D.path u ω) =ᶠ[𝓝[{u : ℝ | 0 ≤ u ∧ (u : WithTop ℝ) < D.lifetime ω}] t]
      (fun u => (D m).pair.Y u ω) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hU] with u hu hUu
    exact hp m u hu.1 hUu
  exact ((D m).pair.ito_Y.continuous_path ω).continuousWithinAt.congr_of_eventuallyEq heq
    (hp m t ht.1 hm)

/-- If the lifetime is finite, the actual assembled path leaves every bounded
state ball before it. This is an escape criterion, not a nonexplosion claim. -/
theorem ae_finite_lifetime_escape : ∀ᵐ ω ∂P, D.lifetime ω ≠ ⊤ →
    ∀ B : ℝ, ∃ t : ℝ, 0 ≤ t ∧ (t : WithTop ℝ) < D.lifetime ω ∧ B ≤ ‖D.path t ω‖ := by
  filter_upwards [D.ae_finite_before_next_exit, D.ae_path_eq_of_le_exit] with ω hnext hp hfinite B
  obtain ⟨m, hm⟩ := exists_nat_gt B
  have hmf : D.exit m ω ≠ ⊤ := ne_top_of_le_ne_top hfinite (D.exit_le_lifetime m ω)
  obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp hmf
  have hu0 : 0 ≤ u := by
    have hn := (D m).pair.exit_nonneg ((m : ℝ)+1) ω
    change (0 : WithTop ℝ) ≤ D.exit m ω at hn
    rw [← hu] at hn
    exact_mod_cast hn
  have hu_lt : (u : WithTop ℝ) < D.lifetime ω :=
    (hnext m u hu0 hu.le).trans_le (D.exit_le_lifetime (m+1) ω)
  obtain ⟨t, ht, hn⟩ := (Probability.exitTime_le_iff
    ((D m).pair.ito_Y.continuous_path ω) ((m : ℝ)+1) u).mp hu.ge
  have htm : (t : WithTop ℝ) ≤ D.exit m ω := by
    rw [← hu]
    exact_mod_cast ht.2
  refine ⟨t, ht.1, (show (t : WithTop ℝ) ≤ (u : WithTop ℝ) by exact_mod_cast ht.2).trans_lt hu_lt, ?_⟩
  rw [hp m t ht.1 htm]
  exact (by linarith : B ≤ (m : ℝ)+1).trans hn

end KLS.LocalDiffusion.LocalProcessFamily
end
#print axioms KLS.LocalDiffusion.LocalProcessFamily.measurable_path_slice
#print axioms KLS.LocalDiffusion.LocalProcessFamily.ae_continuousOn_before_lifetime
#print axioms KLS.LocalDiffusion.LocalProcessFamily.ae_finite_lifetime_escape
