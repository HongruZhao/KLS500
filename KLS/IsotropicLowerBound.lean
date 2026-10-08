import KLS.DefinitionBridges
import KLS.OptimalConstants

/-!
# The isotropic coordinate-test lower bound

For any probability measure on a positive-dimensional Euclidean space with
the stated isotropic first and second moments, a coordinate is a locally
Lipschitz L² test with variance one and Dirichlet energy one.  Consequently
its optimal Poincaré constant is at least one, including when it is infinite.
No log-concavity or KLS upper bound is assumed.
-/

open scoped ENNReal NNReal
open MeasureTheory InnerProductSpace

noncomputable section
namespace KLS

variable {n : ℕ} {μ : Measure (Space n)}

/-- A coordinate is globally Lipschitz, hence is an eligible locally
Lipschitz test whenever it is in L². -/
theorem locallyLipschitz_coordinate (i : Fin n) :
    LocallyLipschitz (fun x : Space n => x i) :=
  (EuclideanSpace.proj i : Space n →L[ℝ] ℝ).lipschitzWith.locallyLipschitz

/-- The actual library gradient of a coordinate is its Euclidean unit vector,
at every point. This computation requires no a.e. gradient convention. -/
theorem gradient_coordinate (i : Fin n) (x : Space n) :
    gradient (fun y : Space n => y i) x = PiLp.single 2 i (1 : ℝ) := by
  apply (toDual ℝ (Space n)).injective
  rw [toDual_gradient]
  change fderiv ℝ (EuclideanSpace.proj i) x = toDual ℝ (Space n) _
  rw [ContinuousLinearMap.fderiv]
  ext y
  simp [EuclideanSpace.inner_single_left]

/-- A coordinate has unit energy under any probability measure. -/
theorem energy_coordinate [IsProbabilityMeasure μ] (i : Fin n) :
    energy μ (fun x : Space n => x i) = 1 := by
  simp [energy, gradient_coordinate]

theorem IsIsotropic.coordinate_test (hμ : IsIsotropic μ) (i : Fin n) :
    LocallyLipschitzTests μ (fun x : Space n => x i) :=
  ⟨locallyLipschitz_coordinate i, hμ.memLp_coordinate i⟩

/-- Every finite admissible Poincaré constant is at least one, by testing any
one coordinate. -/
theorem IsIsotropic.one_le_of_poincare_constant [IsProbabilityMeasure μ]
    (hμ : IsIsotropic μ) (i : Fin n) {C : ℝ≥0}
    (hC : C ∈ poincareConstants μ) : (1 : ℝ≥0∞) ≤ (C : ℝ≥0∞) := by
  have h := hC (fun x : Space n => x i) (hμ.coordinate_test i)
  simpa [hμ.variance_coordinate i, energy_coordinate] using h

/-- Isotropy forces the actual extended optimal Poincaré constant to be at
least one. The theorem remains valid if the finite constant set is empty. -/
theorem IsIsotropic.one_le_poincareConstant [IsProbabilityMeasure μ]
    (hμ : IsIsotropic μ) (hn : 1 ≤ n) : 1 ≤ poincareConstant μ := by
  let i : Fin n := ⟨0, by omega⟩
  apply le_poincareConstant_of_forall
  intro C hC
  exact hμ.one_le_of_poincare_constant i hC

theorem IsIsotropic.poincareConstant_pos [IsProbabilityMeasure μ]
    (hμ : IsIsotropic μ) (hn : 1 ≤ n) : 0 < poincareConstant μ :=
  lt_of_lt_of_le (by norm_num) (hμ.one_le_poincareConstant hn)

/-- The lower bound applies directly to the full compact-set log-concave
class, using only its probability and isotropy fields. -/
theorem admissibleMeasure.one_le_poincareConstant (hμ : admissibleMeasure μ)
    (hn : 1 ≤ n) : 1 ≤ poincareConstant μ := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  exact hμ.isotropic.one_le_poincareConstant hn

theorem admissibleMeasure.poincareConstant_pos (hμ : admissibleMeasure μ)
    (hn : 1 ≤ n) : 0 < poincareConstant μ := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  exact hμ.isotropic.poincareConstant_pos hn

end KLS
end

#print axioms KLS.gradient_coordinate
#print axioms KLS.energy_coordinate
#print axioms KLS.IsIsotropic.one_le_poincareConstant
#print axioms KLS.IsIsotropic.poincareConstant_pos
#print axioms KLS.admissibleMeasure.one_le_poincareConstant
