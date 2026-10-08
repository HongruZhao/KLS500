import KLS.FullPoincareStrongApproximation
import KLS.WeightedTaylorSpectralCriterion
import KLS.ConvexUpperTestHessian
import KLS.SmoothBarrierStability
import KLS.IsotropicLowerBound

/-! The literal full-class consequence of a universal regular Taylor estimate. -/
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped Topology ContDiff ENNReal NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

theorem coordinateHessian_lower_of_strongConvexOn
    {V : Space n → ℝ} (hV : ContDiff ℝ 2 V) {κ : ℝ}
    (hc : StrongConvexOn univ κ V) (x : Space n) (a : Fin n → ℝ) :
    κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a) := by
  let q := centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) (0 : Space n) 0 0
  let F := fun y => V y + (-κ) * q y + 0
  have hq : ContDiff ℝ 2 q := (contDiff_centeredQuadratic _ _ _ _).of_le (by simp)
  have hF : ContDiff ℝ 2 F := (hV.add (contDiff_const.mul hq)).add contDiff_const
  have hconv : ConvexOn ℝ univ F := by
    convert strongConvexOn_iff_convex.mp hc using 1
    funext y
    simp only [F, q, centeredQuadratic, sub_zero, inner_zero_left, zero_add, add_zero,
      matrixAction_one_apply, real_inner_self_eq_norm_sq]
    ring
  have hp := coordinateHessian_posSemidef_of_convex_upper_touch hconv hF.contDiffAt
    (x₀ := x) rfl (Eventually.of_forall fun _ => le_rfl)
  have he : coordinateHessian F x = coordinateHessian V x + (-κ) • (1 : Matrix (Fin n) (Fin n) ℝ) :=
    coordinateHessian_add_scalar_quadratic_const hV 0 (-κ) 0 x
  rw [he] at hp
  have ha := hp.dotProduct_mulVec_nonneg a
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, star_trivial, smul_eq_mul, neg_mul] at ha
  linarith

/-- This remains conditional on the stated universal Taylor bound. The same
explicit numerical constant passes through actual approximating laws and the
entire original locally Lipschitz test class. -/
theorem admissibleMeasure.poincareConstant_le_of_global_regular_Taylor
    (hn : 0 < n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {R : ℝ} (hR : 1 ≤ R)
    (hTaylor : ∀ (V : Space n → ℝ) (κ : ℝ), IsProbabilityMeasure (potentialMeasure V) →
      ContDiff ℝ (⊤ : ℕ∞) V → 0 < κ → StrongConvexOn univ κ V →
      IsIsotropic (potentialMeasure V) → WeightedCoordinateTaylorBound V R) :
    poincareConstant μ ≤ ENNReal.ofReal (439804651110400 * R ^ 2) := by
  let C : ℝ≥0 := Real.toNNReal (439804651110400 * R ^ 2)
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hC : 0 < C := Real.toNNReal_pos.mpr (by positivity)
  have hmem : C ∈ poincareConstants μ := by
    apply hμ.mem_poincareConstants_of_global_strongDensity hC
    intro ν hν hs
    obtain ⟨V, κ, hV, hκ, hc, heq⟩ := hs
    let : IsProbabilityMeasure (potentialMeasure V) := heq ▸ hν.isProb
    have hiso : IsIsotropic (potentialMeasure V) := heq ▸ hν.isotropic
    have hbound := poincareConstant_le_of_isotropic_weightedCoordinateTaylorBound hn hV hκ
      (coordinateHessian_lower_of_strongConvexOn (hV.of_le (by simp)) hc) hiso hR
      (hTaylor V κ inferInstance hV hκ hc hiso)
    have hne : (poincareConstants (potentialMeasure V)).Nonempty :=
      poincareConstants_nonempty_iff.mpr (hbound.trans_lt ENNReal.ofReal_lt_top)
    rw [heq]
    apply (poincareConstants_iff_optimal_le hne (hiso.poincareConstant_pos (by omega))).mpr
    exact hbound
  exact poincareConstant_le_of_mem hmem

end KLS
end
