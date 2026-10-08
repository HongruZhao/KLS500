import Mathlib

/-!
Current-mathlib consumer lemmas for a càdlàg zero-jump SDE solution and its
continuous stochastic-integral version. These use only right continuity on
nonnegative times. No Brownian, SDE, existence, or equality premise is hidden.
-/

open MeasureTheory Filter Topology

namespace KLS

variable {Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [TopologicalSpace E] [T2Space E]

/-- Per-time almost-sure equality of two processes with almost-sure right-continuous
paths on nonnegative times implies indistinguishability on that time domain. -/
theorem ae_all_eq_nonneg_of_rightCont {A B : ℝ → Ω → E}
    (hA : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => A s ω) (nhdsWithin t (Set.Ioi t)) (𝓝 (A t ω)))
    (hB : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => B s ω) (nhdsWithin t (Set.Ioi t)) (𝓝 (B t ω)))
    (h : ∀ t : ℝ, 0 ≤ t → A t =ᵐ[P] B t) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → A t ω = B t ω := by
  have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → A (q : ℝ) ω = B (q : ℝ) ω := by
    rw [ae_all_iff]
    intro q
    by_cases hq : 0 ≤ (q : ℝ)
    · filter_upwards [h (q : ℝ) hq] with ω hω
      exact fun _ => hω
    · exact Eventually.of_forall fun _ hq' => absurd hq' hq
  filter_upwards [hA, hB, hrat] with ω hAω hBω hqω
  intro t ht
  have hex : ∀ k : ℕ, ∃ q : ℚ, t < (q : ℝ) ∧ (q : ℝ) < t + 1 / ((k : ℝ) + 1) := by
    intro k
    exact exists_rat_btwn (lt_add_of_pos_right t (by positivity : 0 < 1 / ((k : ℝ) + 1)))
  choose q hq1 hq2 using hex
  have htend : Tendsto (fun k : ℕ => (q k : ℝ)) atTop (nhdsWithin t (Set.Ioi t)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall fun k => hq1 k⟩
    have hupper : Tendsto (fun k : ℕ => t + 1 / ((k : ℝ) + 1)) atTop (𝓝 t) := by
      simpa using (tendsto_const_nhds (x := t) (f := atTop (α := ℕ))).add
        tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun k => (hq1 k).le) (fun k => (hq2 k).le)
  have h1 := (hAω t ht).comp htend
  have h2 := (hBω t ht).comp htend
  have heq : ((fun s => A s ω) ∘ fun k : ℕ => (q k : ℝ)) =
      ((fun s => B s ω) ∘ fun k : ℕ => (q k : ℝ)) :=
    funext fun k => hqω (q k) (ht.trans (hq1 k).le)
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

/-- A right-continuous process which agrees at every fixed nonnegative time with a
continuous version has continuous paths on `[0,∞)` almost surely, and the two
processes agree on that entire domain outside one null set. -/
theorem ae_continuousOn_nonneg_of_continuous_version {X Y : ℝ → Ω → E}
    (hX : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => X s ω) (nhdsWithin t (Set.Ioi t)) (𝓝 (X t ω)))
    (hY : ∀ ω, Continuous fun t => Y t ω)
    (hmod : ∀ t : ℝ, 0 ≤ t → X t =ᵐ[P] Y t) :
    ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Ici 0) ∧
      ∀ t : ℝ, 0 ≤ t → X t ω = Y t ω := by
  have hpath := ae_all_eq_nonneg_of_rightCont hX
    (Eventually.of_forall fun ω t _ => (hY ω).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds) hmod
  filter_upwards [hpath] with ω hω
  exact ⟨(hY ω).continuousOn.congr (fun t ht => hω t ht), hω⟩

omit [TopologicalSpace E] [T2Space E] in
/-- Indistinguishability on nonnegative times permits evaluation at an arbitrary
almost-surely nonnegative random time, without exchanging uncountable AE quantifiers. -/
theorem ae_eq_at_nonnegative_random_time {X Y : ℝ → Ω → E} {τ : Ω → ℝ}
    (hpath : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → X t ω = Y t ω)
    (hτ : ∀ᵐ ω ∂P, 0 ≤ τ ω) :
    (fun ω => X (τ ω) ω) =ᵐ[P] fun ω => Y (τ ω) ω := by
  filter_upwards [hpath, hτ] with ω hω hτω
  exact hω (τ ω) hτω

#print axioms ae_all_eq_nonneg_of_rightCont
#print axioms ae_continuousOn_nonneg_of_continuous_version
#print axioms ae_eq_at_nonnegative_random_time

end KLS
