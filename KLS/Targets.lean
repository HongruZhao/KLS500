import KLS.Definitions

/-!
# Full verification targets -- statements, not proofs

The definitions below fix the intended quantifiers without adding axioms.
No inhabitant of these propositions is asserted. The original density-based
Cheeger target `KLS.KLSConjecture` is imported unchanged from `KLS.Definitions`.
The full measure-class bridge remains a separate obligation.
-/

open scoped ENNReal NNReal
open MeasureTheory

namespace KLS

/-- Finite energy must imply L² membership, not merely an inequality whose
real integrals could otherwise take default values. -/
def FullFiniteEnergyPoincare (C : ℝ≥0∞) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ μ : Measure (Space n), admissibleMeasure μ →
    ∀ f : Space n → ℝ, LocallyLipschitz f → energy μ f < ⊤ →
      MemLp f 2 μ ∧ variance μ f ≤ C * energy μ f

/-- L² convention; energy is permitted to be infinite. -/
def FullL2Poincare (C : ℝ≥0∞) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ μ : Measure (Space n), admissibleMeasure μ →
    ∀ f : Space n → ℝ, LocallyLipschitzTests μ f →
      variance μ f ≤ C * energy μ f

/-- Full Poincaré task, explicitly using the imported optimal constants.
The numerical upper bound is a finite positive real chosen before every
dimension, measure, and test function. This is a target proposition only. -/
def FullPoincareVerification : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧
    universalPoincareConstant ≤ ENNReal.ofReal C₀ ∧
    universalPoincareConstant < ⊤ ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ μ : Measure (Space n), admissibleMeasure μ →
      1 ≤ poincareConstant μ ∧ poincareConstant μ ≤ universalPoincareConstant) ∧
    FullFiniteEnergyPoincare universalPoincareConstant ∧
    FullL2Poincare universalPoincareConstant

/-- Full compact-set-log-concave Cheeger target, in addition to the exact
existing density-based `KLSConjecture`. -/
def FullCheegerVerification : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ μ : Measure (Space n), admissibleMeasure μ →
      ENNReal.ofReal c₀ ≤ cheegerConstant μ) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ μ : Measure (Space n), IsKLSMeasure μ →
      ENNReal.ofReal c₀ ≤ cheegerConstant μ)

/-- Exact sharpness requires a separately specified finite number; neither
an infimum definition nor a nonsharp upper bound proves this proposition. -/
def SharpPoincareValue (Csharp : ℝ) : Prop :=
  0 < Csharp ∧ universalPoincareConstant = ENNReal.ofReal Csharp

end KLS
