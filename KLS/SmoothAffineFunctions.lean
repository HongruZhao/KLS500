import KLS.IsotropicAffineL2

/-! Compact smooth functions minus affine functions retain smoothness,
bounded actual Hessians, and linear growth. -/

open MeasureTheory
open scoped ContDiff BigOperators
noncomputable section
namespace KLS
set_option maxHeartbeats 1000000

variable {n : ℕ}

def SmoothAffineFunction (f : Space n → ℝ) : Prop :=
  ∃ g : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
    ∃ (c : ℝ) (L : Space n →L[ℝ] ℝ), f = fun x => g x - c - L x

lemma SmoothAffineFunction.contDiff {f : Space n → ℝ} (hf : SmoothAffineFunction f) :
    ContDiff ℝ (⊤ : ℕ∞) f := by
  obtain ⟨g, hg, _, c, L, rfl⟩ := hf
  exact (hg.sub contDiff_const).sub L.contDiff

lemma SmoothAffineFunction.const_mul {f : Space n → ℝ} (hf : SmoothAffineFunction f) (a : ℝ) :
    SmoothAffineFunction (fun x => a * f x) := by
  obtain ⟨g, hg, hc, c, L, rfl⟩ := hf
  refine ⟨fun x => a * g x, contDiff_const.mul hg, hc.mul_left, a * c, a • L, ?_⟩
  ext x
  simp only [_root_.smul_apply, smul_eq_mul]
  ring

lemma SmoothAffineFunction.exists_linear_growth {f : Space n → ℝ}
    (hf : SmoothAffineFunction f) : ∃ A B : ℝ, ∀ x, |f x| ≤ A + B * ‖x‖ := by
  obtain ⟨g, hg, hc, c, L, rfl⟩ := hf
  obtain ⟨A, hA⟩ := hg.continuous.bounded_above_of_compact_support hc
  refine ⟨A + |c|, ‖L‖, fun x => ?_⟩
  calc
    |g x - c - L x| ≤ |g x - c| + |L x| := abs_sub _ _
    _ ≤ (|g x| + |c|) + |L x| := add_le_add (abs_sub _ _) le_rfl
    _ ≤ (A + |c|) + ‖L‖ * ‖x‖ := by
      gcongr
      · exact hA x
      · exact L.le_opNorm x

lemma secondFrechet_sub_affine {g : Space n → ℝ}
    (hg : ContDiff ℝ 2 g) (c : ℝ) (L : Space n →L[ℝ] ℝ) (x : Space n) :
    fderiv ℝ (fderiv ℝ (fun y => g y - c - L y)) x = fderiv ℝ (fderiv ℝ g) x := by
  have hd := hg.differentiable (by norm_num)
  have he : fderiv ℝ (fun y => g y - c - L y) = fun y => fderiv ℝ g y - L := by
    funext y
    change fderiv ℝ ((fun y => g y - c) - (L : Space n → ℝ)) y = _
    rw [fderiv_sub ((hd y).sub_const c) L.differentiableAt, fderiv_sub_const, L.fderiv]
  rw [he, fderiv_sub_const]

lemma SmoothAffineFunction.exists_hessian_bound {f : Space n → ℝ}
    (hf : SmoothAffineFunction f) : ∃ M : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M := by
  obtain ⟨g, hg, hc, c, L, rfl⟩ := hf
  obtain ⟨M, _, hM⟩ := hc.exists_bound_iteratedFDeriv hg 2
  refine ⟨M, fun x => ?_⟩
  rw [secondFrechet_sub_affine (hg.of_le (by simp)) c L x]
  rw [← norm_iteratedFDeriv_one (fderiv ℝ g), norm_iteratedFDeriv_fderiv]
  exact hM 2 le_rfl x

def affineCoordinateLinearPart {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : IsIsotropic μ) (f : Lp ℝ 2 μ) : Space n →L[ℝ] ℝ :=
  ∑ j : Fin n, inner ℝ (isotropicAffineCoordinate hμ (some j)) f • EuclideanSpace.proj j

lemma affineRemoval_eq_sub_affine {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : IsIsotropic μ) (f : Lp ℝ 2 μ) (g : Space n → ℝ) :
    affineRemoval hμ f g = fun x => g x - inner ℝ (isotropicAffineCoordinate hμ none) f -
      affineCoordinateLinearPart hμ f x := by
  funext x
  simp only [affineRemoval, Fintype.sum_option, affineCoordinateFunction, Option.elim_none,
    Option.elim_some, mul_one, affineCoordinateLinearPart, _root_.sum_apply,
    _root_.smul_apply, smul_eq_mul]
  change g x - (inner ℝ (isotropicAffineCoordinate hμ none) f +
    ∑ j : Fin n, inner ℝ (isotropicAffineCoordinate hμ (some j)) f * x j) =
    g x - inner ℝ (isotropicAffineCoordinate hμ none) f -
    ∑ j : Fin n, inner ℝ (isotropicAffineCoordinate hμ (some j)) f * x j
  ring

lemma smoothAffineFunction_affineRemoval {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : IsIsotropic μ) (f : Lp ℝ 2 μ) {g : Space n → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) :
    SmoothAffineFunction (affineRemoval hμ f g) :=
  ⟨g, hg, hc, _, _, affineRemoval_eq_sub_affine hμ f g⟩

end KLS
end
#print axioms KLS.SmoothAffineFunction.exists_hessian_bound
#print axioms KLS.smoothAffineFunction_affineRemoval
