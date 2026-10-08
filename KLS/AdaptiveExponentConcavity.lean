import KLS.AdaptiveCovarianceGenerator
import KLS.ConcaveExponentialTilt

/-! Positive semidefinite quadratic parameters give actual concave exponents. -/
open MeasureTheory Set Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
variable {n : ℕ}

theorem exponent_affine_gap (c : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (x y : Space n) (t : ℝ) :
    exponent c Q (t • x + (1-t) • y) = t * exponent c Q x + (1-t) * exponent c Q y +
      t * (1-t) / 2 * dotProduct (fun i => x i-y i) (Q *ᵥ (fun i => x i-y i)) := by
  simp only [exponent_eq_dotProduct]
  change c ⬝ᵥ (t • (fun i => x i) + (1-t) • (fun i => y i)) -
      (t • (fun i => x i) + (1-t) • (fun i => y i)) ⬝ᵥ
        (Q *ᵥ (t • (fun i => x i) + (1-t) • (fun i => y i))) / 2 =
    t * (c ⬝ᵥ (fun i => x i) - (fun i => x i) ⬝ᵥ (Q *ᵥ (fun i => x i)) / 2) +
    (1-t) * (c ⬝ᵥ (fun i => y i) - (fun i => y i) ⬝ᵥ (Q *ᵥ (fun i => y i)) / 2) +
    t * (1-t) / 2 * ((fun i => x i) - (fun i => y i)) ⬝ᵥ
      (Q *ᵥ ((fun i => x i) - (fun i => y i)))
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub,
    add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    sub_dotProduct, dotProduct_sub, smul_eq_mul]
  ring

theorem concaveOn_exponent (c : Fin n → ℝ) {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.PosSemidef) : ConcaveOn ℝ univ (exponent c Q) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hb' : b = 1-a := by linarith
  subst b
  change a * exponent c Q x + (1-a) * exponent c Q y ≤ exponent c Q (a • x + (1-a) • y)
  rw [exponent_affine_gap]
  have hn : 0 ≤ dotProduct (fun i => x i-y i) (Q *ᵥ (fun i => x i-y i)) := by
    simpa only [Pi.star_apply, star_trivial] using hQ.dotProduct_mulVec_nonneg (fun i => x i-y i)
  exact le_add_of_nonneg_right (mul_nonneg (div_nonneg (mul_nonneg ha hb) (by norm_num)) hn)

/-- The literal normalized quadratic-tilt law is log-concave for Q positive
semidefinite. The original density representation is the only density premise. -/
theorem law_measureLogConcave_of_density {μ : Measure (Space n)} (hμ : HasLogConcaveDensity μ)
    (c : Fin n → ℝ) {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosSemidef) :
    measureLogConcave (law μ c Q) :=
  hμ.measureLogConcave_tilted (continuous_exponent c Q) (concaveOn_exponent c hQ)

/-- For the requested original compact-set isotropic class, its density is
provided by the independently proved full-class equivalence. -/
theorem law_measureLogConcave_of_admissible {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (c : Fin n → ℝ) {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosSemidef) :
    measureLogConcave (law μ c Q) :=
  law_measureLogConcave_of_density hμ.hasLogConcaveDensity c hQ

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.concaveOn_exponent
#print axioms KLS.AdaptiveLocalization.law_measureLogConcave_of_admissible
