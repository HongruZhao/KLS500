import KLS.LocalFamilyRegularity

/-! The assembly's localization times are its own actual first norm exits. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
namespace KLS.LocalDiffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open Probability
universe u v

/-- Agreement through the first exit of a continuous path determines that exit,
even when the second path is only defined by a local assembly. -/
theorem exitTime_eq_of_eq_before_exit {E : Type v} [NormedAddCommGroup E]
    {f g : ℝ → E} (hf : Continuous f) (r : ℝ)
    (he : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) ≤ exitTime (fun (_ : Unit) => f) r () → g t = f t) :
    exitTime (fun (_ : Unit) => g) r () = exitTime (fun (_ : Unit) => f) r () := by
  classical
  by_cases htop : exitTime (fun (_ : Unit) => f) r () = ⊤
  · have hsets : exitSet (fun (_ : Unit) => g) r () = exitSet (fun (_ : Unit) => f) r () := by
      ext t
      constructor <;> intro ht
      · exact ⟨ht.1, by change r ≤ ‖f t‖; rw [← he t ht.1 (by rw [htop]; exact le_top)]; exact ht.2⟩
      · exact ⟨ht.1, by change r ≤ ‖g t‖; rw [he t ht.1 (by rw [htop]; exact le_top)]; exact ht.2⟩
    simp only [exitTime, hsets]
  · obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp htop
    obtain ⟨u, hu, hfu⟩ := (exitTime_le_iff hf r v).mp hv.ge
    have huτ : (u : WithTop ℝ) ≤ exitTime (fun (_ : Unit) => f) r () := by
      rw [← hv]
      exact_mod_cast hu.2
    have hgu : u ∈ exitSet (fun (_ : Unit) => g) r () :=
      ⟨hu.1, by change r ≤ ‖g u‖; rw [he u hu.1 huτ]; exact hfu⟩
    have hgne : (exitSet (fun (_ : Unit) => g) r ()).Nonempty := ⟨u, hgu⟩
    have hinf : sInf (exitSet (fun (_ : Unit) => g) r ()) = v := by
      apply le_antisymm ((csInf_le (bddBelow_exitSet _ _ _) hgu).trans hu.2)
      apply le_csInf hgne
      intro s hs
      by_contra hvs
      have hsv : s < v := lt_of_not_ge hvs
      have hsτ : (s : WithTop ℝ) ≤ exitTime (fun (_ : Unit) => f) r () := by
        rw [← hv]
        exact_mod_cast hsv.le
      have hfs : r ≤ ‖f s‖ := by rw [← he s hs.1 hsτ]; exact hs.2
      have hτs := (exitTime_le_iff (X := fun (_ : Unit) => f) (ω := ()) hf r s).mpr ⟨s, ⟨hs.1, le_rfl⟩, hfs⟩
      rw [← hv] at hτs
      exact hsv.not_ge (by exact_mod_cast hτs)
    calc exitTime (fun (_ : Unit) => g) r () = (v : WithTop ℝ) := by
          rw [exitTime, if_pos hgne, hinf]
      _ = _ := hv

namespace LocalProcessFamily
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {N d : ℕ} {W : MultidimBrownianMotion P d} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
  {b : (Fin N → ℝ) → Fin N → ℝ} {s : Fin d → (Fin N → ℝ) → Fin N → ℝ}
  (D : LocalProcessFamily W ℱ hW b s)

/-- Every localization time is almost surely the first norm exit of the assembled path. -/
theorem ae_exit_eq_path : ∀ᵐ ω ∂P, ∀ m : ℕ,
    D.exit m ω = Probability.exitTime (fun ω t => D.path t ω) ((m : ℝ)+1) ω := by
  filter_upwards [D.ae_path_eq_of_le_exit] with ω hp m
  exact (exitTime_eq_of_eq_before_exit ((D m).pair.ito_Y.continuous_path ω)
    ((m : ℝ)+1) (hp m)).symm

end LocalProcessFamily
end KLS.LocalDiffusion
end
#print axioms KLS.LocalDiffusion.LocalProcessFamily.ae_exit_eq_path
