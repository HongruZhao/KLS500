import KLS.FiniteFeatureAverage
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Matrix.Normed

/-! Smoothness of actual matrix inversion from its determinant/adjugate formula,
using the elementwise finite-dimensional matrix norm. -/
open Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} {A : E → Matrix (Fin n) (Fin n) ℝ}

theorem contDiff_det_of_entries
    (hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p => A p i j)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => (A p).det) := by
  simp_rw [Matrix.det_apply']
  exact ContDiff.sum (fun σ _ => contDiff_const.mul
    (contDiff_prod (fun i _ => hA (σ i) i)))

theorem contDiff_adjugate_entry_of_entries
    (hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p => A p i j)) (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => (A p).adjugate i j) := by
  simp_rw [Matrix.adjugate_apply]
  apply contDiff_det_of_entries
  intro a b
  by_cases h : a = j
  · subst a
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simpa only [Matrix.updateRow_ne h] using hA a b

theorem contDiff_inverse_entry_of_entries
    (hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p => A p i j))
    (hdet : ∀ p, (A p).det ≠ 0) (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => (A p)⁻¹ i j) := by
  simp_rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  exact ((contDiff_det_of_entries hA).inv hdet).mul
    (contDiff_adjugate_entry_of_entries hA i j)

theorem contDiff_inverse_of_entries
    (hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p => A p i j))
    (hdet : ∀ p, (A p).det ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => (A p)⁻¹) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact contDiff_inverse_entry_of_entries hA hdet i j

end KLS
end
#print axioms KLS.contDiff_inverse_of_entries
