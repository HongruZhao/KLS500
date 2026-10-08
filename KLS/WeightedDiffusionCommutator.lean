import KLS.WeightedDiffusionCalculus

/-!
# The concrete derivative--diffusion commutator

Under C² regularity of the potential and C³ regularity of the test function,
actual coordinate derivatives satisfy `D_i Lφg = Lφ(D_i g) - Σ_j φ_ij D_j g`.
Mixed derivative commutation is proved from the Fréchet Hessian symmetry theorem.
-/

open MeasureTheory InnerProductSpace
open scoped BigOperators ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

lemma coordinateDerivative_sub {f g : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    coordinateDerivative (fun y => f y - g y) i x =
      coordinateDerivative f i x - coordinateDerivative g i x := by
  unfold coordinateDerivative
  rw [fderiv_fun_sub hf hg]
  simp

lemma coordinateDerivative_mul {f g : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    coordinateDerivative (fun y => f y * g y) i x =
      coordinateDerivative f i x * g x + f x * coordinateDerivative g i x := by
  unfold coordinateDerivative
  rw [fderiv_fun_mul hf hg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

lemma coordinateDerivative_sum {α : Type*} [Fintype α] {f : α → Space n → ℝ} {x : Space n}
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) (i : Fin n) :
    coordinateDerivative (fun y => ∑ j, f j y) i x =
      ∑ j, coordinateDerivative (f j) i x := by
  unfold coordinateDerivative
  rw [fderiv_fun_sum (fun j _ => hf j)]
  simp

lemma contDiff_coordinateHessian {g : Space n → ℝ} {k m : ℕ∞ω}
    (hg : ContDiff ℝ k g) (hm : m + 2 ≤ k) (i j : Fin n) :
    ContDiff ℝ m (fun x => coordinateHessian g x i j) := by
  exact contDiff_coordinateDerivative
    (contDiff_coordinateDerivative hg (m := m + 1) (by convert hm using 1; norm_num [add_assoc]) j)
    (by rfl) i

lemma contDiff_weightedDiffusion {φ g : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hg : ContDiff ℝ 3 g) :
    ContDiff ℝ 1 (weightedDiffusion φ g) := by
  have heq : weightedDiffusion φ g = fun x => ∑ i,
      (coordinateHessian g x i i - coordinateDerivative g i x * coordinateDerivative φ i x) :=
    funext (weightedDiffusion_eq_sum φ g)
  rw [heq]
  apply ContDiff.sum
  intro i _
  exact (contDiff_coordinateHessian hg (m := 1) (by norm_num) i i).sub
    ((contDiff_coordinateDerivative hg (m := 1) (by norm_num) i).mul
      (contDiff_coordinateDerivative hφ (m := 1) (by norm_num) i))

/-- The third coordinate derivatives commute in the arrangement used by the Laplacian. -/
lemma coordinateDerivative_diagonal_eq {g : Space n → ℝ} (hg : ContDiff ℝ 3 g)
    (i j : Fin n) (x : Space n) :
    coordinateDerivative (fun y => coordinateHessian g y j j) i x =
      coordinateHessian (coordinateDerivative g i) x j j := by
  have hgj : ContDiff ℝ 2 (coordinateDerivative g j) :=
    contDiff_coordinateDerivative hg (by norm_num) j
  have hsymm := (coordinateHessian_symmetric hgj x).apply i j
  have hsymm_g : coordinateDerivative (coordinateDerivative g j) i =
      coordinateDerivative (coordinateDerivative g i) j := by
    funext y
    exact ((coordinateHessian_symmetric (hg.of_le (by norm_num)) y).apply i j).symm
  change coordinateHessian (coordinateDerivative g j) x i j = _
  rw [← hsymm]
  change coordinateDerivative (coordinateDerivative (coordinateDerivative g j) i) j x = _
  rw [hsymm_g]
  rfl

/-- The derivative of the concrete diffusion, including the Hessian drift correction. -/
theorem coordinateDerivative_weightedDiffusion {φ g : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hg : ContDiff ℝ 3 g) (i : Fin n) (x : Space n) :
    coordinateDerivative (weightedDiffusion φ g) i x =
      weightedDiffusion φ (coordinateDerivative g i) x -
        ∑ j, coordinateHessian φ x i j * coordinateDerivative g j x := by
  have heq : weightedDiffusion φ g = fun y => ∑ j,
      (coordinateHessian g y j j - coordinateDerivative g j y * coordinateDerivative φ j y) :=
    funext (weightedDiffusion_eq_sum φ g)
  have hdg (j : Fin n) : DifferentiableAt ℝ (coordinateDerivative g j) x :=
    (contDiff_coordinateDerivative hg (m := 1) (by norm_num) j).differentiable
      (by norm_num) x
  have hdφ (j : Fin n) : DifferentiableAt ℝ (coordinateDerivative φ j) x :=
    (contDiff_coordinateDerivative hφ (m := 1) (by norm_num) j).differentiable
      (by norm_num) x
  have hddg (j : Fin n) : DifferentiableAt ℝ (fun y => coordinateHessian g y j j) x :=
    (contDiff_coordinateHessian hg (m := 1) (by norm_num) j j).differentiable
      (by norm_num) x
  rw [heq, coordinateDerivative_sum
    (f := fun j y => coordinateHessian g y j j - coordinateDerivative g j y * coordinateDerivative φ j y)
    (fun j => (hddg j).sub ((hdg j).mul (hdφ j)))]
  rw [weightedDiffusion_eq_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [coordinateDerivative_sub (f := fun y => coordinateHessian g y j j)
    (g := fun y => coordinateDerivative g j y * coordinateDerivative φ j y)
    (hddg j) ((hdg j).mul (hdφ j)),
    coordinateDerivative_mul (hdg j) (hdφ j), coordinateDerivative_diagonal_eq hg]
  have hsymm := (coordinateHessian_symmetric (hg.of_le (by norm_num)) x).apply i j
  change coordinateHessian (coordinateDerivative g i) x j j -
    (coordinateHessian g x i j * coordinateDerivative φ j x +
      coordinateDerivative g j x * coordinateHessian φ x i j) = _
  change coordinateHessian g x j i = coordinateHessian g x i j at hsymm
  rw [← hsymm]
  change coordinateHessian (coordinateDerivative g i) x j j -
    (coordinateDerivative (coordinateDerivative g i) j x * coordinateDerivative φ j x +
      coordinateDerivative g j x * coordinateHessian φ x i j) = _
  ring

end KLS
end

#print axioms KLS.contDiff_weightedDiffusion
#print axioms KLS.coordinateDerivative_diagonal_eq
#print axioms KLS.coordinateDerivative_weightedDiffusion
