import KLS.SuspensionCoordinates

/-! The actual pushforward suspension has a log-concave density after the
explicit Euclidean coordinate change. -/

open MeasureTheory Set Matrix
open scoped ENNReal BigOperators ContDiff
noncomputable section
namespace KLS

lemma hasLogConcaveDensity_euclideanSuspensionLaw {n N : ℕ} {V f : Space n → ℝ}
    (hV : Measurable V) (hf : Measurable f) [IsProbabilityMeasure (potentialMeasure V)]
    {β σ c : ℝ} (hβ : 0 < β) (hσ : 0 < σ)
    (hc : ConvexOn ℝ univ (suspensionPotential (I := Fin N) V f β σ c)) :
    HasLogConcaveDensity (euclideanSuspensionLaw (N := N) (potentialMeasure V) f β σ c) := by
  let W : Space (suspensionDimension n N) → ℝ := fun z =>
    suspensionPotential V f β σ c (suspensionInverseLinear n N z) - Real.log (σ * β / 2)
  have hW : ConvexOn ℝ univ W := by
    convert (hc.comp_linearMap (suspensionInverseLinear n N)).add_const
      (-Real.log (σ * β / 2)) using 1
    · ext z
      rfl
    · ext z
      simp [W, sub_eq_add_neg]
  have hpos : 0 < σ * β / 2 := by positivity
  have he (z : Space (suspensionDimension n N)) :
      expNegPotential (W z : WithTop ℝ) = ENNReal.ofReal (σ * β / 2 * Real.exp
        (-suspensionPotential V f β σ c (suspensionInverseLinear n N z))) := by
    simp only [expNegPotential, W, neg_sub, Real.exp_sub, Real.exp_log hpos]
    rw [Real.exp_neg]
    congr 1
  refine ⟨(fun z => (W z : WithTop ℝ)), ?_, ?_, ?_⟩
  · simpa [ExtendedConvex] using hW.convex_epigraph
  · simp_rw [he]
    have hi := (suspensionCoordinates n N).symm.measurable
    change Measurable (fun z => ENNReal.ofReal (σ * β / 2 * Real.exp
      (-suspensionPotential V f β σ c
        (((suspensionCoordinates n N).symm z).2, ((suspensionCoordinates n N).symm z).1))))
    unfold suspensionPotential
    fun_prop
  · simp_rw [he]
    exact euclideanSuspensionLaw_eq_withDensity hV hf hσ

/-- A concrete positive copy count gives the actual log-concave suspension
for every positive noise rate; no abstract suspended law is postulated. -/
theorem exists_logConcave_euclideanSuspensionLaw {n : ℕ} {V f : Space n → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    [IsProbabilityMeasure (potentialMeasure V)] {κ M β : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hbound : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (hβ : 0 < β) :
    ∃ N : ℕ, 0 < N ∧ ∀ σ : ℝ, 0 < σ →
      HasLogConcaveDensity (euclideanSuspensionLaw (N := N)
        (potentialMeasure V) f β σ (Real.sqrt N)⁻¹) := by
  obtain ⟨N, hN, hc⟩ := exists_convex_suspensionPotential hV hf hκ hlower hbound hβ.le
  exact ⟨N, hN, fun σ hσ => hasLogConcaveDensity_euclideanSuspensionLaw
    hV.continuous.measurable hf.continuous.measurable hβ hσ (hc σ)⟩

end KLS
end
#print axioms KLS.hasLogConcaveDensity_euclideanSuspensionLaw
#print axioms KLS.exists_logConcave_euclideanSuspensionLaw
