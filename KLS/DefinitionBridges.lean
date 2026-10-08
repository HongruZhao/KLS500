import KLS.Definitions

/-!
# Elementary semantic bridges for the KLS definitions

These lemmas certify density absolute continuity, measurability of compact-set
interpolation, and the intended first and second moments of isotropy. They do
not establish equivalence between the density and compact-set log-concave
classes, nor do they prove either KLS bound.
-/

open scoped ENNReal NNReal BigOperators
open MeasureTheory Set

noncomputable section
namespace KLS

variable {n : ℕ} {μ : Measure (Space n)}

/-- Absolute continuity in the original Job 45 class follows from its density
representation, without a smoothness or positivity condition on the density. -/
theorem HasLogConcaveDensity.absolutelyContinuousLebesgue
    (hμ : HasLogConcaveDensity μ) : AbsolutelyContinuousLebesgue μ := by
  obtain ⟨V, _, _, rfl⟩ := hμ
  exact withDensity_absolutelyContinuous _ _

/-- Constant density on a measurable convex set is represented by a finite
constant potential on the set and `+∞` outside. This permits nonsmooth support;
normalization and isotropy are separate properties. -/
theorem hasLogConcaveDensity_convex_indicator {S : Set (Space n)}
    (hS : Convex ℝ S) (hSm : MeasurableSet S) (c : ℝ) :
    HasLogConcaveDensity ((volume : Measure (Space n)).withDensity
      (S.indicator (fun _ => ENNReal.ofReal (Real.exp (-c))))) := by
  classical
  let V : Space n → WithTop ℝ := fun x => if x ∈ S then (c : WithTop ℝ) else ⊤
  have hV : ExtendedConvex V := by
    have hepi : {p : Space n × ℝ | V p.1 ≤ (p.2 : WithTop ℝ)} = S ×ˢ Ici c := by
      ext p
      by_cases hp : p.1 ∈ S <;> simp [V, hp]
    rw [ExtendedConvex, hepi]
    exact hS.prod (convex_Ici c)
  have hdensity : (fun x => expNegPotential (V x)) =
      S.indicator (fun _ => ENNReal.ofReal (Real.exp (-c))) := by
    funext x
    by_cases hx : x ∈ S <;> simp [V, expNegPotential, hx]
  refine ⟨V, hV, ?_, ?_⟩
  · rw [hdensity]
    exact measurable_const.indicator hSm
  · rw [hdensity]

/-- The compact-set formulation only measures Borel sets. -/
theorem isCompact_affineSetCombination (t : ℝ) {E F : Set (Space n)}
    (hE : IsCompact E) (hF : IsCompact F) :
    IsCompact (affineSetCombination t E F) := by
  exact (hE.prod hF).image (by fun_prop)

theorem measurableSet_affineSetCombination (t : ℝ) {E F : Set (Space n)}
    (hE : IsCompact E) (hF : IsCompact F) :
    MeasurableSet (affineSetCombination t E F) :=
  (isCompact_affineSetCombination t hE hF).measurableSet

/-- The first-moment integrability in isotropy includes every coordinate. -/
theorem IsIsotropic.integrable_coordinate (hμ : IsIsotropic μ) (i : Fin n) :
    Integrable (fun x : Space n => x i) μ := by
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hμ.1

theorem IsIsotropic.integral_coordinate (hμ : IsIsotropic μ) (i : Fin n) :
    (∫ x : Space n, x i ∂μ) = 0 := by
  calc
    (∫ x : Space n, x i ∂μ) =
        (EuclideanSpace.proj i) (∫ x : Space n, x ∂μ) :=
      (EuclideanSpace.proj i).integral_comp_comm hμ.1
    _ = 0 := by rw [hμ.2.1]; simp

theorem IsIsotropic.integrable_coordinate_sq (hμ : IsIsotropic μ) (i : Fin n) :
    Integrable (fun x : Space n => (x i) ^ 2) μ := by
  simpa only [pow_two] using hμ.2.2.1 i i

theorem IsIsotropic.memLp_coordinate (hμ : IsIsotropic μ) (i : Fin n) :
    MemLp (fun x : Space n => x i) 2 μ := by
  exact (memLp_two_iff_integrable_sq (by fun_prop)).2 (hμ.integrable_coordinate_sq i)

theorem IsIsotropic.integral_coordinate_sq (hμ : IsIsotropic μ) (i : Fin n) :
    (∫ x : Space n, (x i) ^ 2 ∂μ) = 1 := by
  have hi := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i i) hμ.2.2.2
  simpa [secondMomentMatrix, pow_two] using hi

/-- Coordinate second-moment integrability gives finite total second moment
in every finite dimension. -/
theorem IsIsotropic.integrable_norm_sq (hμ : IsIsotropic μ) :
    Integrable (fun x : Space n => ‖x‖ ^ 2) μ := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  exact integrable_finsetSum Finset.univ (fun i _ => hμ.integrable_coordinate_sq i)

theorem IsIsotropic.integral_norm_sq (hμ : IsIsotropic μ) :
    (∫ x : Space n, ‖x‖ ^ 2 ∂μ) = (n : ℝ) := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum Finset.univ (fun i _ => hμ.integrable_coordinate_sq i)]
  simp [hμ.integral_coordinate_sq]

/-- Each coordinate has unit extended variance. The probability and L²
hypotheses are available before invoking the real variance formula. -/
theorem IsIsotropic.variance_coordinate [IsProbabilityMeasure μ]
    (hμ : IsIsotropic μ) (i : Fin n) :
    variance μ (fun x : Space n => x i) = 1 := by
  rw [variance, ← ProbabilityTheory.ofReal_variance (hμ.memLp_coordinate i)]
  rw [ProbabilityTheory.variance_eq_sub (hμ.memLp_coordinate i)]
  change ENNReal.ofReal ((∫ x : Space n, (x i) ^ 2 ∂μ) -
    (∫ x : Space n, x i ∂μ) ^ 2) = 1
  rw [hμ.integral_coordinate_sq i, hμ.integral_coordinate i]
  norm_num

end KLS
end

#print axioms KLS.HasLogConcaveDensity.absolutelyContinuousLebesgue
#print axioms KLS.IsIsotropic.integral_norm_sq
#print axioms KLS.IsIsotropic.variance_coordinate

#print axioms KLS.hasLogConcaveDensity_convex_indicator
