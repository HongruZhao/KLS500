import KLS.ContactCapLocalization
import KLS.SubgradientAffineCovariance

/-! The actual contact tilt changes subgradient images only by translation,
so local Alexandrov density constants apply uniformly to every tilt. -/

open MeasureTheory InnerProductSpace Set
open scoped ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem volume_convexSubgradientImage_contactTilt
    (u : Space n → ℝ) (x p z v : Space n) (c t : ℝ) (S : Set (Space n)) :
    volume (convexSubgradientImage (contactTilt u x p z v c t) S) =
      volume (convexSubgradientImage u S) := by
  have heq : contactTilt u x p z v c t = fun y =>
      u y + inner ℝ (-(p + t • v)) y +
        (-u x + inner ℝ p x + t * inner ℝ v z - t * c) := by
    funext y
    simp only [contactTilt, supportGap, inner_sub_right, inner_neg_left,
      inner_add_left, real_inner_smul_left]
    ring
  rw [heq, volume_convexSubgradientImage_add_affine]

/-- The same local constants control the actual tilted potential on each
of its confined sections. -/
theorem contactTiltSection_subgradient_volume_bounds
    {u : Space n → ℝ} {x p z v : Space n} {R c t : ℝ} {a b : ℝ≥0∞}
    (hlower : ∀ S : Set (Space n), IsCompact S → S ⊆ {y | u y ≤ R} →
      a * volume S ≤ volume (convexSubgradientImage u S))
    (hupper : ∀ S : Set (Space n), IsOpen S → S ⊆ {y | u y ≤ R} →
      volume (convexSubgradientImage u S) ≤ b * volume S) :
    (∀ S : Set (Space n), IsCompact S → S ⊆ contactTiltSection u x p z v R c t →
      a * volume S ≤ volume (convexSubgradientImage (contactTilt u x p z v c t) S)) ∧
    (∀ S : Set (Space n), IsOpen S → S ⊆ contactTiltSection u x p z v R c t →
      volume (convexSubgradientImage (contactTilt u x p z v c t) S) ≤ b * volume S) := by
  constructor
  · intro S hS hsub
    rw [volume_convexSubgradientImage_contactTilt]
    exact hlower S hS (fun y hy => (hsub hy).1)
  · intro S hS hsub
    rw [volume_convexSubgradientImage_contactTilt]
    exact hupper S hS (fun y hy => (hsub hy).1)

end KLS
end

#print axioms KLS.volume_convexSubgradientImage_contactTilt
#print axioms KLS.contactTiltSection_subgradient_volume_bounds
