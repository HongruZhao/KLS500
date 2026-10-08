import KLS.LocalProcessFamily

/-! A jointly measurable path assembled from the actual countable local family. -/
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

/-- The coordinatewise limsup of the genuine stopped representatives. On the
common event of compatibility this is eventually constant before the lifetime. -/
def path (t : ℝ) (ω : Ω) (i : Fin N) : ℝ :=
  Filter.limsup (fun m : ℕ => Probability.stopped (D.exit m)
    (fun ω u => (D m).pair.Y u ω i) ω t) Filter.atTop

theorem measurable_path : Measurable (Function.uncurry fun ω t => D.path t ω) := by
  apply Measurable.of_eval
  intro i
  exact Measurable.limsup fun m => Probability.measurable_uncurry_stopped
    (D.exit_isStoppingTime m) ((D m).pair.ito_Y.measurable_uncurry_comp (measurable_pi_apply i))

theorem progressive_path (i : Fin N) :
    Probability.ProgressivelyMeasurable ℱ (fun ω t => D.path t ω i) :=
  Probability.ProgressivelyMeasurable.limsup fun m =>
    Probability.ProgressivelyMeasurable.stopped (D.exit_isStoppingTime m)
      ((D m).pair.ito_Y.progressivelyMeasurable_comp (continuous_apply i))

/-- Each finite time up to a radius-m exit lies strictly before the next exit. -/
theorem ae_finite_before_next_exit : ∀ᵐ ω ∂P, ∀ m : ℕ, ∀ t : ℝ, 0 ≤ t →
    (t : WithTop ℝ) ≤ D.exit m ω → (t : WithTop ℝ) < D.exit (m+1) ω := by
  have heq (m : ℕ) : (D m).pair.exit ((m : ℝ)+1) =ᵐ[P]
      (D (m+1)).pair.exit ((m : ℝ)+1) :=
    ae_exit_eq (D m) (D (m+1)) ((m : ℝ)+1) (by positivity) le_rfl (by push_cast; linarith)
  have hzero : ∀ᵐ ω ∂P, ∀ m : ℕ, (D m).pair.Y 0 ω = 0 :=
    ae_all_iff.mpr fun m => (D m).initial_Y
  have heqs := ae_all_iff.mpr heq
  filter_upwards [hzero, heqs] with ω h0 he m t ht htm
  apply lt_of_not_ge
  intro hle
  obtain ⟨u, hu, hn⟩ := (Probability.exitTime_le_iff
    ((D (m+1)).pair.ito_Y.continuous_path ω) (((m+1 : ℕ) : ℝ)+1) t).mp hle
  have hum : (u : WithTop ℝ) ≤ (D (m+1)).pair.exit ((m : ℝ)+1) ω := by
    rw [← he m]
    exact (show (u : WithTop ℝ) ≤ (t : WithTop ℝ) by exact_mod_cast hu.2).trans htm
  have hnorm := norm_le_of_le_exit (D (m+1)) (by positivity : (0 : ℝ) ≤ (m : ℝ)+1)
    hu.1 (h0 (m+1)) hum
  push_cast at hn
  linarith

/-- Agreement includes finite exit endpoints, because a larger ball still applies. -/
theorem ae_path_eq_of_le_exit : ∀ᵐ ω ∂P, ∀ m : ℕ, ∀ t : ℝ, 0 ≤ t →
    (t : WithTop ℝ) ≤ D.exit m ω → D.path t ω = (D m).pair.Y t ω := by
  filter_upwards [D.ae_finite_before_next_exit, D.ae_coherent]
    with ω hnext hc m t ht hm
  funext i
  have he : (fun k : ℕ => Probability.stopped (D.exit k)
      (fun ω u => (D k).pair.Y u ω i) ω t) =ᶠ[atTop] (fun _ => (D m).pair.Y t ω i) := by
    apply eventually_atTop.mpr
    refine ⟨m+1, fun k hk => ?_⟩
    have htk := (hnext m t ht hm).le.trans (hc.1 hk)
    change (if (t : WithTop ℝ) ≤ D.exit k ω then (D k).pair.Y t ω i else 0) = (D m).pair.Y t ω i
    rw [if_pos htk]
    exact (congrFun (hc.2 m k ((Nat.le_succ m).trans hk) t ht hm) i).symm
  exact (Filter.limsup_congr he).trans (by simp)

theorem ae_path_eq_of_lt_exit : ∀ᵐ ω ∂P, ∀ m : ℕ, ∀ t : ℝ, 0 ≤ t →
    (t : WithTop ℝ) < D.exit m ω → D.path t ω = (D m).pair.Y t ω :=
  D.ae_path_eq_of_le_exit.mono fun ω hω m t ht hm => hω m t ht hm.le

theorem path_initial : D.path 0 =ᵐ[P] 0 := by
  filter_upwards [D.ae_path_eq_of_le_exit, (D 0).initial_Y] with ω hp h0
  rw [hp 0 0 le_rfl ((D 0).pair.exit_nonneg _ ω), h0]
  rfl

end KLS.LocalDiffusion.LocalProcessFamily
end
#print axioms KLS.LocalDiffusion.LocalProcessFamily.measurable_path
#print axioms KLS.LocalDiffusion.LocalProcessFamily.progressive_path
#print axioms KLS.LocalDiffusion.LocalProcessFamily.ae_path_eq_of_le_exit
