import KLS.SuspensionFiberLaw
import KLS.SuspensionConvexPotential
import KLS.WeightedIntegrationByParts

/-! Finite independent copies of the original density and the literal joint
suspension density in product coordinates. -/

open MeasureTheory Set
open scoped ENNReal BigOperators
noncomputable section
namespace KLS

lemma pi_withDensity_ofReal_generic {I E : Type*} [Fintype I] [MeasureSpace E]
    [SigmaFinite (volume : Measure E)] (f : I → E → ℝ)
    (hf : ∀ i, Integrable (f i)) (hnn : ∀ i x, 0 ≤ f i x) :
    Measure.pi (fun i => (volume : Measure E).withDensity (fun x => ENNReal.ofReal (f i x))) =
      (volume : Measure (I → E)).withDensity
        (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  change (∫⁻ x, ENNReal.ofReal (∏ i, f i (x i))
    ∂((Measure.pi (fun _ : I => (volume : Measure E))).restrict (univ.pi s))) = _
  rw [Measure.restrict_pi_pi]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod (fun i => (hf i).restrict))
    (Filter.Eventually.of_forall fun x => Finset.prod_nonneg (fun i _ => hnn i (x i)))]
  rw [integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hnn i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hf i).restrict
    (Filter.Eventually.of_forall (hnn i))

lemma pi_potentialMeasure_eq_withDensity {n N : ℕ} {V : Space n → ℝ}
    (hV : Measurable V) [IsProbabilityMeasure (potentialMeasure V)] :
    Measure.pi (fun _ : Fin N => potentialMeasure V) =
      (volume : Measure (Fin N → Space n)).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-(∑ i, V (x i))))) := by
  have hi : Integrable (fun x => Real.exp (-V x)) := by
    simpa only [one_mul] using
      (integrable_potentialMeasure_iff hV).1 (integrable_const (1 : ℝ))
  have h := pi_withDensity_ofReal_generic (fun _ : Fin N => fun x => Real.exp (-V x))
    (fun _ => hi) (fun _ x => Real.exp_nonneg _)
  have he (x : Fin N → Space n) : (∏ i, Real.exp (-V (x i))) =
      Real.exp (-(∑ i, V (x i))) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  simpa only [potentialMeasure, he] using h

/-- The actual law from independent copies and Laplace noise has exactly the
joint density proportional to the convex suspension potential. -/
theorem laplaceSuspensionLaw_potential_density {n N : ℕ} {V f : Space n → ℝ}
    (hV : Measurable V) (hf : Measurable f) [IsProbabilityMeasure (potentialMeasure V)]
    {β σ c : ℝ} (hσ : 0 < σ) :
    laplaceSuspensionLaw (Measure.pi (fun _ : Fin N => potentialMeasure V))
      (fun x => c * ∑ i, f (x i)) β σ =
      (volume : Measure ((Fin N → Space n) × ℝ)).withDensity
        (fun p => ENNReal.ofReal (σ * β / 2 * Real.exp
          (-suspensionPotential V f β σ c (p.2, p.1)))) := by
  rw [laplaceSuspensionLaw_eq_withDensity _ _ (by fun_prop) hσ,
    pi_potentialMeasure_eq_withDensity hV, prod_withDensity_left (by fun_prop),
    ← withDensity_mul _ (by fun_prop) (by
      exact ((continuous_laplaceNoiseDensity β).measurable.comp
        (by fun_prop)).const_mul σ |>.ennreal_ofReal)]
  congr 1
  funext p
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  unfold laplaceNoiseDensity suspensionPotential
  congr 1
  rw [neg_add, Real.exp_add]
  ring

end KLS
end
#print axioms KLS.laplaceSuspensionLaw_potential_density
