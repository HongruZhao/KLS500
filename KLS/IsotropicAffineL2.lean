import KLS.FiniteOrthonormalProjection
import KLS.ThirdCumulant

/-! Constants and coordinates form an actual orthonormal family in L2 of an
isotropic probability law. The finite projection removes precisely the affine
part and has a concrete function representative. -/

open MeasureTheory Filter
open scoped ENNReal BigOperators ContDiff
noncomputable section
namespace KLS

def affineCoordinateFunction {n : ℕ} (a : Option (Fin n)) (x : Space n) : ℝ :=
  Option.elim a 1 (fun j => x j)

lemma IsIsotropic.memLp_affineCoordinate {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) (a : Option (Fin n)) :
    MemLp (affineCoordinateFunction a) 2 μ := by
  cases a with
  | none => exact memLp_const 1
  | some j => exact hμ.memLp_coordinate j

def isotropicAffineCoordinate {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) (a : Option (Fin n)) : Lp ℝ 2 μ :=
  (hμ.memLp_affineCoordinate a).toLp (affineCoordinateFunction a)

lemma isotropicAffineCoordinate_coe {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) (a : Option (Fin n)) :
    (isotropicAffineCoordinate hμ a : Space n → ℝ) =ᵐ[μ] affineCoordinateFunction a :=
  (hμ.memLp_affineCoordinate a).coeFn_toLp

lemma inner_isotropicAffineCoordinate {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) (a : Option (Fin n)) (f : Lp ℝ 2 μ) :
    inner ℝ (isotropicAffineCoordinate hμ a) f =
      ∫ x, affineCoordinateFunction a x * f x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [isotropicAffineCoordinate_coe hμ a] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

lemma orthonormal_isotropicAffineCoordinate {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) :
    Orthonormal ℝ (isotropicAffineCoordinate hμ) := by
  rw [orthonormal_iff_ite]
  intro a b
  rw [inner_isotropicAffineCoordinate]
  have he : (∫ x, affineCoordinateFunction a x * isotropicAffineCoordinate hμ b x ∂μ) =
      ∫ x, affineCoordinateFunction a x * affineCoordinateFunction b x ∂μ :=
    integral_congr_ae (EventuallyEq.rfl.mul (isotropicAffineCoordinate_coe hμ b))
  rw [he]
  cases a with
  | none =>
    cases b with
    | none => simp [affineCoordinateFunction]
    | some j => simpa [affineCoordinateFunction] using hμ.integral_coordinate j
  | some i =>
    cases b with
    | none => simpa [affineCoordinateFunction] using hμ.integral_coordinate i
    | some j => simpa [affineCoordinateFunction] using hμ.integral_coordinate_mul i j

def affineRemoval {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : IsIsotropic μ) (f : Lp ℝ 2 μ) (g : Space n → ℝ) (x : Space n) : ℝ :=
  g x - ∑ a : Option (Fin n), inner ℝ (isotropicAffineCoordinate hμ a) f *
    affineCoordinateFunction a x

lemma memLp_affineRemoval {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : IsIsotropic μ) (f : Lp ℝ 2 μ) {g : Space n → ℝ} (hg : MemLp g 2 μ) :
    MemLp (affineRemoval hμ f g) 2 μ :=
  hg.sub (memLp_finsetSum Finset.univ (fun a _ =>
    (hμ.memLp_affineCoordinate a).const_mul _))

lemma finiteOrthonormalRemainder_affine_coe {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) (f : Lp ℝ 2 μ)
    {g : Space n → ℝ} (hg : (f : Space n → ℝ) =ᵐ[μ] g) :
    (finiteOrthonormalRemainder (isotropicAffineCoordinate hμ) f : Space n → ℝ) =ᵐ[μ]
      affineRemoval hμ f g := by
  rw [finiteOrthonormalRemainder_apply]
  apply (Lp.coeFn_sub _ _).trans
  apply hg.sub
  apply (Lp.coeFn_finsetSum _ _).trans
  have hs : (∑ a : Option (Fin n), ⇑(inner ℝ (isotropicAffineCoordinate hμ a) f •
    isotropicAffineCoordinate hμ a)) =ᵐ[μ]
    (∑ a : Option (Fin n), fun x => inner ℝ (isotropicAffineCoordinate hμ a) f *
      affineCoordinateFunction a x) := by
    apply eventuallyEq_sum
    intro a _
    exact (Lp.coeFn_smul _ _).trans
      ((isotropicAffineCoordinate_coe hμ a).const_smul _)
  filter_upwards [hs] with x hx
  simpa only [Finset.sum_apply] using hx

lemma toLp_affineRemoval {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : IsIsotropic μ) (f : Lp ℝ 2 μ) {g : Space n → ℝ} (hg : MemLp g 2 μ)
    (he : (f : Space n → ℝ) =ᵐ[μ] g) :
    (memLp_affineRemoval hμ f hg).toLp (affineRemoval hμ f g) =
      finiteOrthonormalRemainder (isotropicAffineCoordinate hμ) f := by
  apply Lp.ext
  exact (memLp_affineRemoval hμ f hg).coeFn_toLp.trans
    (finiteOrthonormalRemainder_affine_coe hμ f he).symm

lemma affineRemoval_orthogonal {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : IsIsotropic μ) (f : Lp ℝ 2 μ) {g : Space n → ℝ} (hg : (f : Space n → ℝ) =ᵐ[μ] g)
    (a : Option (Fin n)) :
    (∫ x, affineCoordinateFunction a x * affineRemoval hμ f g x ∂μ) = 0 := by
  have hh := inner_finiteOrthonormalRemainder (orthonormal_isotropicAffineCoordinate hμ) f a
  rw [inner_isotropicAffineCoordinate] at hh
  have he : (∫ x, affineCoordinateFunction a x *
      finiteOrthonormalRemainder (isotropicAffineCoordinate hμ) f x ∂μ) =
      ∫ x, affineCoordinateFunction a x * affineRemoval hμ f g x ∂μ := integral_congr_ae
    (EventuallyEq.rfl.mul (finiteOrthonormalRemainder_affine_coe hμ f hg))
  exact he.symm.trans hh

def affineProjectionVector {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : IsIsotropic μ) (f : Lp ℝ 2 μ) : Space n :=
  WithLp.toLp 2 (fun j => inner ℝ (isotropicAffineCoordinate hμ (some j)) f)

lemma finiteOrthonormalProjection_affine_coe {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) (f : Lp ℝ 2 μ) :
    (finiteOrthonormalProjection (isotropicAffineCoordinate hμ) f : Space n → ℝ) =ᵐ[μ]
      (fun x => inner ℝ (isotropicAffineCoordinate hμ none) f +
        inner ℝ x (affineProjectionVector hμ f)) := by
  rw [finiteOrthonormalProjection_apply]
  have hs : (∑ a : Option (Fin n), ⇑(inner ℝ (isotropicAffineCoordinate hμ a) f •
      isotropicAffineCoordinate hμ a)) =ᵐ[μ]
      (∑ a : Option (Fin n), fun x => inner ℝ (isotropicAffineCoordinate hμ a) f *
        affineCoordinateFunction a x) := by
    apply eventuallyEq_sum
    intro a _
    exact (Lp.coeFn_smul _ _).trans ((isotropicAffineCoordinate_coe hμ a).const_smul _)
  apply (Lp.coeFn_finsetSum _ _).trans
  filter_upwards [hs] with x hx
  rw [hx]
  simp only [Finset.sum_apply, Fintype.sum_option, affineCoordinateFunction,
    Option.elim_none, Option.elim_some, mul_one, inner_eq_coordinate_sum]
  rfl

lemma affineProjectionVector_norm_sq_le {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) (f : Lp ℝ 2 μ) :
    ‖affineProjectionVector hμ f‖ ^ 2 ≤
      ‖finiteOrthonormalProjection (isotropicAffineCoordinate hμ) f‖ ^ 2 := by
  rw [finiteOrthonormalProjection_norm_sq (orthonormal_isotropicAffineCoordinate hμ),
    Fintype.sum_option, EuclideanSpace.real_norm_sq_eq]
  change (∑ j : Fin n, inner ℝ (isotropicAffineCoordinate hμ (some j)) f ^ 2) ≤
    inner ℝ (isotropicAffineCoordinate hμ none) f ^ 2 +
      ∑ j : Fin n, inner ℝ (isotropicAffineCoordinate hμ (some j)) f ^ 2
  exact le_add_of_nonneg_left (sq_nonneg _)

end KLS
end
#print axioms KLS.orthonormal_isotropicAffineCoordinate
#print axioms KLS.toLp_affineRemoval
#print axioms KLS.affineRemoval_orthogonal
