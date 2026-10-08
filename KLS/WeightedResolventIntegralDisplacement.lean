import KLS.WeightedResolventDualDisplacement

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- The actual composition of the symmetric mass resolvent remains symmetric. -/
theorem weightedMassResolvent_square_symmetric {t : ℝ} (ht : 0 < t)
    (f g : Lp ℝ 2 (potentialMeasure φ)) :
    inner ℝ (weightedMassResolvent φ ht (weightedMassResolvent φ ht f)) g =
      inner ℝ f (weightedMassResolvent φ ht (weightedMassResolvent φ ht g)) := by
  rw [weightedMassResolvent_symmetric,weightedMassResolvent_symmetric]

/-- True self-adjointness transfers the dyadic bound to the actual integral
of a faithful test's displacement against a smooth bounded-gradient unit witness. -/
theorem weightedMassResolvent_square_defect_integral_abs_le
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {t : ℝ} (ht : 0 < t) {g : Space n → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg2 : MemLp g 2 (potentialMeasure φ))
    {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hgB : ∀ x, |g x| ≤ B) (hgM : ∀ x, ‖gradient g x‖ ≤ M)
    {ψ w : Space n → ℝ} (hψ : LocallyLipschitzTests (potentialMeasure φ) ψ)
    (heψ : energy (potentialMeasure φ) ψ < ⊤)
    (hw : w =ᵐ[potentialMeasure φ]
      (weightedMassResolvent φ ht (weightedMassResolvent φ ht (hψ.2.toLp ψ)) : Space n → ℝ)) :
    |∫ x, (ψ x-w x)*g x ∂potentialMeasure φ| ≤
      4*B*Real.sqrt t*(∫ x, ‖gradient ψ x‖ ∂potentialMeasure φ) := by
  let F := hψ.2.toLp ψ
  let G := hg2.toLp g
  have hi : (∫ x, (ψ x-w x)*g x ∂potentialMeasure φ) =
      inner ℝ (F-weightedMassResolvent φ ht (weightedMassResolvent φ ht F)) G := by
    rw [L2.real_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [hψ.2.coeFn_toLp,hg2.coeFn_toLp,hw,
      Lp.coeFn_sub F (weightedMassResolvent φ ht (weightedMassResolvent φ ht F))] with x hx hy hz hu
    simp only [hu,Pi.sub_apply,hx,hy,hz,F,G]
  have hs : inner ℝ (F-weightedMassResolvent φ ht (weightedMassResolvent φ ht F)) G =
      inner ℝ (G-weightedMassResolvent φ ht (weightedMassResolvent φ ht G)) F := by
    rw [inner_sub_left,inner_sub_left,weightedMassResolvent_square_symmetric]
    exact congrArg₂ (fun a b : ℝ => a-b) (real_inner_comm G F)
      (real_inner_comm (weightedMassResolvent φ ht (weightedMassResolvent φ ht G)) F)
  rw [hi,hs]
  exact weightedMassResolvent_square_dual_displacement_le hφ hconv ht hg hg2 hB hM hgB hgM hψ heψ

end KLS
end
