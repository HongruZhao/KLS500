import KLS.LocalProcessCompatibility

/-! A countable coherent family and its lifetime, built from the actual ball extensions. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
namespace KLS.LocalDiffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {N d : ℕ} {W : MultidimBrownianMotion P d} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
  {b : (Fin N → ℝ) → Fin N → ℝ} {s : Fin d → (Fin N → ℝ) → Fin N → ℝ}

abbrev LocalProcessFamily (W : MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ)
    (b : (Fin N → ℝ) → Fin N → ℝ) (s : Fin d → (Fin N → ℝ) → Fin N → ℝ) :=
  ∀ m : ℕ, LocalProcess W ℱ hW b s ((m : ℝ) + 1)

namespace LocalProcessFamily
variable (D : LocalProcessFamily W ℱ hW b s)

def exit (m : ℕ) : Ω → WithTop ℝ := (D m).exit

def lifetime (ω : Ω) : WithTop ℝ := ⨆ m, D.exit m ω

theorem exit_isStoppingTime (m : ℕ) : IsStoppingTime ℱ (D.exit m) :=
  (D m).exit_isStoppingTime

theorem lifetime_isStoppingTime : IsStoppingTime ℱ D.lifetime := by
  intro t
  have heq : {ω | D.lifetime ω ≤ (t : WithTop ℝ)} = ⋂ m : ℕ, {ω | D.exit m ω ≤ (t : WithTop ℝ)} := by
    ext ω
    simp only [lifetime, Set.mem_setOf_eq, Set.mem_iInter]
    exact ciSup_le_iff (OrderTop.bddAbove _)
  rw [heq]
  exact MeasurableSet.iInter fun m => D.exit_isStoppingTime m t

theorem exit_le_lifetime (m : ℕ) (ω : Ω) : D.exit m ω ≤ D.lifetime ω :=
  le_ciSup (f := fun k => D.exit k ω) (OrderTop.bddAbove _) m

theorem lt_lifetime_iff (ω : Ω) (t : ℝ) :
    (t : WithTop ℝ) < D.lifetime ω ↔ ∃ m, (t : WithTop ℝ) < D.exit m ω :=
  lt_ciSup_iff (OrderTop.bddAbove _)

theorem lifetime_pos : ∀ᵐ ω ∂P, (0 : WithTop ℝ) < D.lifetime ω := by
  filter_upwards [(D 0).exit_pos (by norm_num)] with ω hω
  exact hω.trans_le (D.exit_le_lifetime 0 ω)

/-- On one common event, all integer-radius constructions have increasing exits
and agree through each smaller-radius exit. -/
theorem ae_coherent : ∀ᵐ ω ∂P,
    Monotone (fun m => D.exit m ω) ∧
    ∀ m k : ℕ, m ≤ k → ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) ≤ D.exit m ω →
      (D m).pair.Y t ω = (D k).pair.Y t ω := by
  have hp : ∀ m k : ℕ, m ≤ k → ∀ᵐ ω ∂P,
      D.exit m ω ≤ D.exit k ω ∧
      ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) ≤ D.exit m ω →
        (D m).pair.Y t ω = (D k).pair.Y t ω := by
    intro m k hmk
    have hR : (m : ℝ) + 1 ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmk 1
    have hnon : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    filter_upwards [ae_exit_eq (D m) (D k) ((m : ℝ)+1) hnon le_rfl hR,
      ae_all_eq_before_exit (D m) (D k) ((m : ℝ)+1) hnon le_rfl hR] with ω heq hagree
    exact ⟨heq.trans_le ((D k).pair.exit_mono ω hR), hagree⟩
  have hall : ∀ᵐ ω ∂P, ∀ m k : ℕ, m ≤ k →
      D.exit m ω ≤ D.exit k ω ∧
      ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) ≤ D.exit m ω →
        (D m).pair.Y t ω = (D k).pair.Y t ω := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro k
    by_cases hmk : m ≤ k
    · exact (hp m k hmk).mono fun ω hω _ => hω
    · exact Eventually.of_forall fun _ h => (hmk h).elim
  filter_upwards [hall] with ω hω
  exact ⟨fun m k hmk => (hω m k hmk).1, fun m k hmk => (hω m k hmk).2⟩

theorem ae_pair_agree : ∀ᵐ ω ∂P, ∀ m k : ℕ, ∀ t : ℝ, 0 ≤ t →
    (t : WithTop ℝ) ≤ D.exit m ω → (t : WithTop ℝ) ≤ D.exit k ω →
      (D m).pair.Y t ω = (D k).pair.Y t ω := by
  filter_upwards [D.ae_coherent] with ω hω m k t ht hm hk
  rcases le_total m k with h | h
  · exact hω.2 m k h t ht hm
  · exact (hω.2 k m h t ht hk).symm

end LocalProcessFamily
end KLS.LocalDiffusion
end
#print axioms KLS.LocalDiffusion.LocalProcessFamily.ae_coherent
#print axioms KLS.LocalDiffusion.LocalProcessFamily.lifetime_isStoppingTime
