import KLS.LogConcavityAbsoluteContinuity
import KLS.LogConcaveDensityPotential
import KLS.ConditionalEndpoints

/-!
# Full compact-set class to the exact original density class

The density is constructed from shrinking balls, proved finite everywhere,
and represented by an extended convex potential. The forward class bridge
is unconditional. It removes the absolute-continuity assumption from the
finite-energy endpoint reduction; universal finiteness is still unproved.
-/

open MeasureTheory

noncomputable section
namespace KLS

theorem admissibleMeasure.hasLogConcaveDensity {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) : HasLogConcaveDensity μ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hd := hasLogConcaveDensity_of_pointwise (measurable_lowerBallDensity μ)
    hμ.lowerBallDensity_lt_top
    (fun x y t ht0 ht1 => hμ.logConcave.lowerBallDensity_logConcave x y ht0 ht1)
  rw [← hμ.eq_withDensity_lowerBallDensity] at hd
  exact hd

/-- Every measure in the requested full compact-set class satisfies the exact
original Job45 density hypotheses. No regularity restriction is added. -/
theorem admissibleMeasure.isKLSMeasure {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) : IsKLSMeasure μ where
  isProb := hμ.isProb
  absCont := hμ.absolutelyContinuousLebesgue
  logConcave := hμ.hasLogConcaveDensity
  isotropic := hμ.isotropic

theorem fullClassAbsolutelyContinuous : FullClassAbsolutelyContinuous := by
  intro n hn μ hμ
  exact hμ.absolutelyContinuousLebesgue

/-- The full finite-energy endpoint now requires only the central unresolved
universal finiteness theorem. Absolute continuity has been proved above. -/
theorem fullFiniteEnergyPoincare_of_universal_finite
    (hfinite : universalPoincareConstant < ⊤) :
    FullFiniteEnergyPoincare universalPoincareConstant :=
  fullFiniteEnergyPoincare_of_finite_and_absolutelyContinuous hfinite
    fullClassAbsolutelyContinuous

end KLS
end

#print axioms KLS.admissibleMeasure.isKLSMeasure
#print axioms KLS.fullClassAbsolutelyContinuous
#print axioms KLS.fullFiniteEnergyPoincare_of_universal_finite
