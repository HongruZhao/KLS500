import KLS.WeightedResolventSquarePairing

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- A literal uniformly bounded gradient pairs against the actual L1 gradient
of every faithful finite-energy test, with all integral domains derived. -/
theorem abs_sum_integral_coordinateDerivative_le {h ψ : Space n → ℝ} {K : ℝ}
    (heψ : energy (potentialMeasure φ) ψ < ⊤)
    (hK : ∀ x, ‖gradient h x‖ ≤ K) :
    |∑ i : Fin n, ∫ x, coordinateDerivative h i x*coordinateDerivative ψ i x ∂potentialMeasure φ| ≤
      K*(∫ x, ‖gradient ψ x‖ ∂potentialMeasure φ) := by
  have hh2 (i : Fin n) : MemLp (coordinateDerivative h i) 2 (potentialMeasure φ) := by
    apply MemLp.of_bound (measurable_coordinateDerivative h i).aestronglyMeasurable K
    exact Eventually.of_forall fun x => (norm_coordinateDerivative_le h i x).trans (hK x)
  have hψ2 (i : Fin n) := memLp_coordinateDerivative_of_energy_lt_top heψ i
  have hp (i : Fin n) : Integrable (fun x => coordinateDerivative h i x*coordinateDerivative ψ i x)
      (potentialMeasure φ) := (hh2 i).integrable_mul (hψ2 i)
  have hg2 : MemLp (gradient ψ) 2 (potentialMeasure φ) :=
    (memLp_two_iff_integrable_sq_norm (measurable_gradient ψ).aestronglyMeasurable).mpr
      (integrable_gradient_norm_sq_of_energy_lt_top heψ)
  have hgI := (hg2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).norm
  rw [← integral_finsetSum Finset.univ (fun i _ => hp i)]
  simp_rw [sum_coordinateDerivative_mul]
  have hb := norm_integral_le_of_norm_le
    (f := fun x => inner ℝ (gradient h x) (gradient ψ x)) (hgI.const_mul K)
    (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using
        (abs_real_inner_le_norm (gradient h x) (gradient ψ x)).trans
          (mul_le_mul_of_nonneg_right (hK x) (norm_nonneg (gradient ψ x))))
  simpa only [Real.norm_eq_abs,integral_const_mul] using hb

/-- The actual squared resolvent difference has the required L1-gradient dual
bound; smooth bounded-gradient forcing is explicit and its gradient bound drops out. -/
theorem weightedMassResolvent_square_sub_inner_abs_le
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s ≤ t) {g : Space n → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg2 : MemLp g 2 (potentialMeasure φ))
    {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hgB : ∀ x, |g x| ≤ B) (hgM : ∀ x, ‖gradient g x‖ ≤ M)
    {ψ : Space n → ℝ} (hψ : LocallyLipschitzTests (potentialMeasure φ) ψ)
    (heψ : energy (potentialMeasure φ) ψ < ⊤) :
    |inner ℝ (weightedMassResolvent φ ht (weightedMassResolvent φ ht (hg2.toLp g))-
      weightedMassResolvent φ hs (weightedMassResolvent φ hs (hg2.toLp g))) (hψ.2.toLp ψ)| ≤
      (t-s)*(B/Real.sqrt (2*t)+B/Real.sqrt (2*s))*(∫ x, ‖gradient ψ x‖ ∂potentialMeasure φ) := by
  obtain ⟨h,hh,_,hhμ,hhG⟩ :=
    weightedMassResolvent_exists_mixed_gradient_bound hφ hconv hs ht hg hg2 hB hM hgB hgM
  rw [weightedMassResolvent_square_sub_inner_eq (hφ.of_le (by simp)) hs ht (hg2.toLp g)
    (hh.of_le (by simp)) hhμ hψ heψ,abs_mul,abs_neg,abs_of_nonneg (sub_nonneg.mpr hst)]
  exact (mul_le_mul_of_nonneg_left (abs_sum_integral_coordinateDerivative_le heψ hhG)
    (sub_nonneg.mpr hst)).trans_eq (by ring)

end KLS
end
