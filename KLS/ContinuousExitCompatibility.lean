import LevyStochCalc.Probability.ExitTime

/-! Deterministic and almost-sure continuity facts for agreement up to exits. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace KLS.LocalDiffusion
open LevyStochCalc.Probability
universe u v
variable {E : Type v} [NormedAddCommGroup E]

/-- Agreement at every rational time strictly before a cutoff extends, by
continuity, to every nonnegative time at or before the cutoff. -/
theorem eq_on_cutoff_of_rat {f g : ℝ → E} (hf : Continuous f) (hg : Continuous g)
    {τ : WithTop ℝ} (h0 : f 0 = g 0)
    (hq : ∀ q : ℚ, 0 < (q : ℝ) → ((q : ℝ) : WithTop ℝ) < τ → f q = g q) :
    ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) ≤ τ → f t = g t := by
  intro t ht hτ
  rcases ht.eq_or_lt with ht | ht
  · simpa only [← ht] using h0
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
  have heq (k : ℕ) : f (q k) = g (q k) := by
    apply hq
    · exact (le_max_left _ _).trans_lt (hqlo k)
    · exact (show ((q k : ℝ) : WithTop ℝ) < (t : WithTop ℝ) by exact_mod_cast hqhi k).trans_le hτ
  have h1 := hf.continuousAt.tendsto.comp hqtend
  have h2 := hg.continuousAt.tendsto.comp hqtend
  exact tendsto_nhds_unique (h1.congr heq) h2

/-- Two continuous paths agreeing up to their common same-radius exit have
exactly the same exit time. -/
theorem exitTime_eq_of_eq_before_common {f g : ℝ → E} (hf : Continuous f) (hg : Continuous g)
    (R : ℝ)
    (heq : ∀ t : ℝ, 0 ≤ t →
      (t : WithTop ℝ) ≤ exitTime (fun (_ : Unit) => f) R () →
      (t : WithTop ℝ) ≤ exitTime (fun (_ : Unit) => g) R () → f t = g t) :
    exitTime (fun (_ : Unit) => f) R () = exitTime (fun (_ : Unit) => g) R () := by
  have hnlt {a b : ℝ → E} (ha : Continuous a) (hb : Continuous b)
      (he : ∀ t : ℝ, 0 ≤ t →
        (t : WithTop ℝ) ≤ exitTime (fun (_ : Unit) => a) R () →
        (t : WithTop ℝ) ≤ exitTime (fun (_ : Unit) => b) R () → a t = b t) :
      ¬ exitTime (fun (_ : Unit) => a) R () < exitTime (fun (_ : Unit) => b) R () := by
    intro hlt
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
    have hle : exitTime (fun (_ : Unit) => a) R () ≤ (t : WithTop ℝ) := ht.ge
    obtain ⟨s, hs, hn⟩ := (exitTime_le_iff ha R t).mp hle
    have hsle : (s : WithTop ℝ) ≤ exitTime (fun (_ : Unit) => a) R () := by
      rw [← ht]
      exact_mod_cast hs.2
    have hsb := hsle.trans hlt.le
    have hb' : exitTime (fun (_ : Unit) => b) R () ≤ (t : WithTop ℝ) :=
      (exitTime_le_iff hb R t).mpr ⟨s, hs, by rw [← he s hs.1 hsle hsb]; exact hn⟩
    exact (not_le_of_gt hlt) (hb'.trans ht.le)
  exact le_antisymm (le_of_not_gt (hnlt hg hf fun t ht htg htf => (heq t ht htf htg).symm))
    (le_of_not_gt (hnlt hf hg heq))

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

/-- Fixed-time almost-sure agreement before a cutoff becomes one common event
of agreement at every time up to the cutoff, using only countably many rationals. -/
theorem ae_all_eq_before_cutoff {X Y : ℝ → Ω → E} {τ : Ω → WithTop ℝ}
    (hX : ∀ ω, Continuous (fun t => X t ω)) (hY : ∀ ω, Continuous (fun t => Y t ω))
    (h0 : X 0 =ᵐ[P] Y 0)
    (h : ∀ t : ℝ, 0 < t → ∀ᵐ ω ∂P, (t : WithTop ℝ) ≤ τ ω → X t ω = Y t ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) ≤ τ ω → X t ω = Y t ω := by
  have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < (q : ℝ) → ((q : ℝ) : WithTop ℝ) < τ ω → X q ω = Y q ω := by
    apply ae_all_iff.mpr
    intro q
    by_cases hq : 0 < (q : ℝ)
    · filter_upwards [h q hq] with ω hω
      exact fun _ hτ => hω hτ.le
    · exact Eventually.of_forall fun _ hq' => (hq hq').elim
  filter_upwards [h0, hrat] with ω h0ω hratω
  exact eq_on_cutoff_of_rat (hX ω) (hY ω) h0ω hratω

end KLS.LocalDiffusion
#print axioms KLS.LocalDiffusion.ae_all_eq_before_cutoff
#print axioms KLS.LocalDiffusion.exitTime_eq_of_eq_before_common
