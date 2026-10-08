import KLS.AdaptiveMaximalLocalProcess
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Positivity of the quadratic parameter along the actual local process. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal BigOperators Topology MatrixOrder Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
universe u
variable {n : ℕ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (Space n)} [IsProbabilityMeasure μ]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ} {R : ℝ}

namespace BallProcess
variable (D : BallProcess μ W ℱ hW R)

theorem matrix_equation_integral (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit ω →
      (D.parameterPath T ω).2 =
        ∫ t in Icc (0 : ℝ) T, inverseCovariance μ (D.parameterPath t ω) ∂volume := by
  have he : ∀ᵐ ω ∂P, ∀ i j : Fin n, (T : WithTop ℝ) ≤ D.exit ω →
      (D.parameterPath T ω).2 i j =
        ∫ t in Icc (0 : ℝ) T, inverseCovariance μ (D.parameterPath t ω) i j ∂volume :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => D.matrix_equation i j hT
  filter_upwards [he] with ω hω hle
  have hint : IntegrableOn (fun t => inverseCovariance μ (D.parameterPath t ω)) (Icc (0 : ℝ) T) volume := ((contDiff_inverseCovariance hμ hfull).continuous.comp
    (D.parameterPath_continuous ω)).integrableOn_Icc
  ext i j
  have hc := ((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj i : Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Fin n → ℝ))).integral_comp_comm hint
  exact (hω i j hle).trans hc

theorem matrix_posSemidef_fixed (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit ω → (D.parameterPath T ω).2.PosSemidef := by
  filter_upwards [D.matrix_equation_integral hμ hfull hT] with ω hω hle
  rw [hω hle]
  letI : OrderClosedTopology (Matrix (Fin n) (Fin n) ℝ) := Matrix.instOrderClosedTopology
  apply Matrix.nonneg_iff_posSemidef.mp
  exact integral_nonneg fun t => (inverseCovariance_posDef hμ hfull _).posSemidef.nonneg

/-- Positivity holds on one common event, including every finite exit endpoint. -/
theorem ae_all_matrix_posSemidef (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) ≤ D.exit ω →
      (D.parameterPath t ω).2.PosSemidef := by
  have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < (q : ℝ) →
      ((q : ℝ) : WithTop ℝ) ≤ D.exit ω → (D.parameterPath q ω).2.PosSemidef := by
    apply ae_all_iff.mpr
    intro q
    by_cases hq : 0 < (q : ℝ)
    · exact (D.matrix_posSemidef_fixed hμ hfull hq).mono fun _ h _ => h
    · exact Eventually.of_forall fun _ h => (hq h).elim
  filter_upwards [hrat, D.parameterPath_initial] with ω hq h0 t ht hle
  rcases ht.eq_or_lt with ht | ht
  · rw [← ht, h0]
    exact Matrix.PosSemidef.zero
  have hex : ∀ k : ℕ, ∃ q : ℚ,
      max 0 (t - 1 / ((k : ℝ) + 1)) < (q : ℝ) ∧ (q : ℝ) < t := by
    intro k
    apply exists_rat_btwn
    apply max_lt ht
    have hp : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  choose q hqlo hqhi using hex
  have hqtend : Tendsto (fun k : ℕ => (q k : ℝ)) atTop (𝓝 t) := by
    have hlow : Tendsto (fun k : ℕ => t - 1 / ((k : ℝ) + 1)) atTop (𝓝 t) := by
      simpa using (tendsto_const_nhds (x := t)).sub tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun k => (le_max_right _ _).trans (hqlo k).le) (fun k => (hqhi k).le)
  letI : OrderClosedTopology (Matrix (Fin n) (Fin n) ℝ) := Matrix.instOrderClosedTopology
  apply Matrix.nonneg_iff_posSemidef.mp
  apply ge_of_tendsto (((D.parameterPath_continuous ω).snd.continuousAt.tendsto).comp hqtend)
  exact Eventually.of_forall fun k => (hq (q k)
    ((le_max_left _ _).trans_lt (hqlo k))
    ((show ((q k : ℝ) : WithTop ℝ) ≤ (t : WithTop ℝ) by exact_mod_cast (hqhi k).le).trans hle)).nonneg

end BallProcess

namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW)

/-- The actual maximal adaptive process has a positive semidefinite quadratic
parameter at every time strictly before its lifetime, on one common event. -/
theorem ae_all_matrix_posSemidef (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < D.lifetime ω →
      (D.parameterPath t ω).2.PosSemidef := by
  have hall : ∀ᵐ ω ∂P, ∀ m : ℕ, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) ≤ D.exit m ω →
      (BallProcess.parameterPath (D m) t ω).2.PosSemidef :=
    ae_all_iff.mpr fun m => BallProcess.ae_all_matrix_posSemidef (D m) hμ hfull
  filter_upwards [hall, D.ae_path_eq_of_le_exit] with ω hω hp t ht hlife
  obtain ⟨m, hm⟩ := (D.lt_lifetime_iff ω t).mp hlife
  have h := hω m t ht hm.le
  simpa only [parameterPath, BallProcess.parameterPath, hp m t ht hm.le] using h

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.BallProcess.ae_all_matrix_posSemidef
#print axioms KLS.AdaptiveLocalization.MaximalProcess.ae_all_matrix_posSemidef
