import KLS.LocalWeakFiniteProduct
import KLS.MatrixLogDet

open MeasureTheory Set Filter Matrix
open scoped BigOperators ContDiff Topology ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

def determinantDirectionalPolynomial (A D : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
    ∑ i : Fin n, (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, A (σ j) j) * D (σ i) i

/-- The literal Leibniz polynomial derivative equals the genuine Frechet
derivative at every matrix, including singular matrices. -/
theorem determinantDirectionalPolynomial_eq_fderiv
    (A D : Matrix (Fin n) (Fin n) ℝ) :
    determinantDirectionalPolynomial A D = fderiv ℝ Matrix.det A D := by
  have he (σ : Equiv.Perm (Fin n)) (j : Fin n) :
      HasDerivAt (fun t : ℝ => A (σ j) j + t * D (σ j) j) (D (σ j) j) 0 := by
    simpa only [one_mul, id_eq] using ((hasDerivAt_id (0 : ℝ)).mul_const (D (σ j) j)).const_add (A (σ j) j)
  have hp (σ : Equiv.Perm (Fin n)) :
      HasDerivAt (fun t : ℝ => ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ j : Fin n, (A (σ j) j + t * D (σ j) j))
        (((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ i : Fin n, (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, A (σ j) j) * D (σ i) i) 0 := by
    have h := (HasDerivAt.fun_finsetProd (u := Finset.univ) (fun j _ => he σ j)).const_mul
      (((Equiv.Perm.sign σ : ℤ) : ℝ))
    simpa only [zero_mul, add_zero, smul_eq_mul] using h
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ => hp σ)
  have hfunc : (fun t : ℝ => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
      ∏ j : Fin n, (A (σ j) j + t * D (σ j) j)) = fun t => (A + t • D).det := by
    funext t
    simp only [Matrix.det_apply', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hfunc] at hs
  have hline : HasDerivAt (fun t : ℝ => A + t • D) D 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const D).const_add A
  have hd : HasFDerivAt Matrix.det (fderiv ℝ Matrix.det A) (A + (0 : ℝ) • D) := by
    simpa only [zero_smul, add_zero] using
      (MatrixCalculus.contDiff_det.differentiable (by simp) A).hasFDerivAt
  exact hs.unique (hd.comp_hasDerivAt 0 hline)

theorem memLp_top_matrixDet {A : Space n → Matrix (Fin n) (Fin n) ℝ}
    {μ : Measure (Space n)} (hA : ∀ i j, MemLp (fun x => A x i j) ∞ μ) :
    MemLp (fun x => (A x).det) ∞ μ := by
  have hterm (σ : Equiv.Perm (Fin n)) :
      MemLp (fun x => ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ j : Fin n, A x (σ j) j) ∞ μ :=
    (memLp_top_finset_product Finset.univ (fun j _ => hA (σ j) j)).const_mul _
  simpa only [Matrix.det_apply'] using memLp_finsetSum Finset.univ (fun σ _ => hterm σ)

theorem memLp_two_determinantDirectionalPolynomial
    {A D : Space n → Matrix (Fin n) (Fin n) ℝ} {μ : Measure (Space n)}
    (hA : ∀ i j, MemLp (fun x => A x i j) ∞ μ)
    (hD : ∀ i j, MemLp (fun x => D x i j) 2 μ) :
    MemLp (fun x => determinantDirectionalPolynomial (A x) (D x)) 2 μ := by
  apply memLp_finsetSum
  intro σ _
  exact (memLp_two_finset_product_derivative Finset.univ
    (fun j _ => hA (σ j) j) (fun j _ => hD (σ j) j)).const_mul _

/-- Differentiation of the actual determinant is obtained solely from its
finite polynomial and the proved local weak product rule. -/
theorem hasLocalWeakCoordinateDerivative_matrixDet
    {A D : Space n → Matrix (Fin n) (Fin n) ℝ} {k : Fin n}
    (hD : ∀ i j, HasLocalWeakCoordinateDerivative (fun x => A x i j) (fun x => D x i j) k)
    (hA : ∀ i j K, IsCompact K → MemLp (fun x => A x i j) ∞ (volume.restrict K))
    (hDloc : ∀ i j K, IsCompact K → MemLp (fun x => D x i j) 2 (volume.restrict K)) :
    HasLocalWeakCoordinateDerivative (fun x => (A x).det)
      (fun x => fderiv ℝ Matrix.det (A x) (D x)) k := by
  let c (σ : Equiv.Perm (Fin n)) : ℝ := ((Equiv.Perm.sign σ : ℤ) : ℝ)
  let P (σ : Equiv.Perm (Fin n)) (x : Space n) := ∏ j : Fin n, A x (σ j) j
  let Q (σ : Equiv.Perm (Fin n)) (x : Space n) :=
    ∑ i : Fin n, (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, A x (σ j) j) * D x (σ i) i
  have hp (σ : Equiv.Perm (Fin n)) : HasLocalWeakCoordinateDerivative (P σ) (Q σ) k :=
    hasLocalWeakCoordinateDerivative_finset_product Finset.univ
      (fun j _ => hD (σ j) j) (fun j _ => hA (σ j) j) (fun j _ => hDloc (σ j) j)
  have hP (σ : Equiv.Perm (Fin n)) : LocallyIntegrable (fun x => c σ * P σ x) volume := by
    apply locallyIntegrable_of_memLp_two_on_compacts
    apply memLp_two_on_compacts_of_top
    intro K hK
    exact (memLp_top_finset_product Finset.univ (fun j _ => hA (σ j) j K hK)).const_mul _
  have hQ (σ : Equiv.Perm (Fin n)) : LocallyIntegrable (fun x => c σ * Q σ x) volume := by
    apply locallyIntegrable_of_memLp_two_on_compacts
    intro K hK
    exact (memLp_two_finset_product_derivative Finset.univ
      (fun j _ => hA (σ j) j K hK) (fun j _ => hDloc (σ j) j K hK)).const_mul _
  have hs := hasLocalWeakCoordinateDerivative_finset_sum Finset.univ
    (fun σ _ => (hp σ).const_mul (c σ)) (fun σ _ => hP σ) (fun σ _ => hQ σ)
  have he : (fun x => ∑ σ : Equiv.Perm (Fin n), c σ * P σ x) = fun x => (A x).det := by
    funext x
    exact (Matrix.det_apply' (A x)).symm
  have hd : (fun x => ∑ σ : Equiv.Perm (Fin n), c σ * Q σ x) =
      fun x => fderiv ℝ Matrix.det (A x) (D x) := by
    funext x
    exact determinantDirectionalPolynomial_eq_fderiv (A x) (D x)
  rwa [he, hd] at hs

end KLS
end
