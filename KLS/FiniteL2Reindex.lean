import KLS.TensorCenteredGradientInverse

/-! Genuine index permutations act isometrically on the actual finite L²
families. Componentwise vector operators commute with tail reindexing. -/

open MeasureTheory
open scoped ENNReal

noncomputable section
namespace KLS
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def finiteL2Reindex {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι') :
    CenteredL2.Family μ ι ≃ₗᵢ[ℝ] CenteredL2.Family μ ι' :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ (Lp ℝ 2 μ) e

@[simp] theorem finiteL2Reindex_apply {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι ≃ ι') (g : CenteredL2.Family μ ι) (i : ι') :
    finiteL2Reindex e g i = g (e.symm i) := rfl

@[simp] theorem finiteL2Reindex_norm {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι ≃ ι') (g : CenteredL2.Family μ ι) : ‖finiteL2Reindex e g‖ = ‖g‖ :=
  (finiteL2Reindex e).norm_map g

theorem finiteL2VectorLift_reindex {J ι ι' : Type*} [Fintype J] [Fintype ι] [Fintype ι']
    (T : Lp ℝ 2 μ →L[ℝ] CenteredL2.Family μ J) (e : ι ≃ ι')
    (g : CenteredL2.Family μ ι) :
    finiteL2VectorLift T ι' (finiteL2Reindex e g) =
      finiteL2Reindex (Equiv.prodCongr (Equiv.refl J) e) (finiteL2VectorLift T ι g) := by
  apply PiLp.ext
  rintro ⟨j, i⟩
  rfl

def tensorFirstSwapEquiv (J ι : Type*) : Equiv.Perm (J × (J × ι)) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun x := (x.2.1, (x.1, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem tensorFirstSwapEquiv_apply {J ι : Type*} (j k : J) (i : ι) :
    tensorFirstSwapEquiv J ι (j, (k, i)) = (k, (j, i)) := rfl

@[simp] theorem tensorFirstSwapEquiv_symm {J ι : Type*} :
    (tensorFirstSwapEquiv J ι).symm = tensorFirstSwapEquiv J ι := rfl

theorem finiteL2Reindex_firstSwap_fixed {J ι : Type*} [Fintype J] [Fintype ι]
    (T : CenteredL2.Family μ (J × (J × ι)))
    (hT : ∀ j k i, T (j, (k, i)) = T (k, (j, i))) :
    finiteL2Reindex (tensorFirstSwapEquiv J ι) T = T := by
  apply PiLp.ext
  rintro ⟨j, k, i⟩
  exact (hT j k i).symm

/-- Distance from an invariant vector controls the actual permutation defect. -/
theorem norm_sub_isometry_apply_sq_le {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (R : E ≃ₗᵢ[ℝ] E) (x y : E) (hy : R y = y) :
    ‖x - R x‖ ^ 2 ≤ 4 * ‖x - y‖ ^ 2 := by
  have he : x - R x = (x - y) - R (x - y) := by rw [map_sub, hy]; abel
  have hb : ‖x - R x‖ ≤ 2 * ‖x - y‖ := by
    rw [he]
    calc
      _ ≤ ‖x - y‖ + ‖R (x - y)‖ := norm_sub_le _ _
      _ = 2 * ‖x - y‖ := by rw [R.norm_map]; ring
  nlinarith [norm_nonneg (x - R x), norm_nonneg (x - y)]

end KLS
end

#print axioms KLS.finiteL2VectorLift_reindex
#print axioms KLS.norm_sub_isometry_apply_sq_le
