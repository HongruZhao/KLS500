import KLS.WeakMatrixDeterminant

open MeasureTheory Set Filter Matrix
open scoped BigOperators ContDiff Topology ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

def adjugateDirectionalPolynomial (A D : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ Matrix.det (A.updateRow j (Pi.single i 1)) (D.updateRow j 0)

theorem memLp_top_matrix_updateRow
    {A : Space n → Matrix (Fin n) (Fin n) ℝ} {μ : Measure (Space n)}
    (hA : ∀ i j, MemLp (fun x => A x i j) ∞ μ) (r : Fin n) (v : Fin n → ℝ) :
    ∀ i j, MemLp (fun x => (A x).updateRow r v i j) ∞ μ := by
  intro i j
  by_cases hi : i = r
  · subst i
    simpa only [Matrix.updateRow_self] using memLp_top_const (v j)
  · simpa only [Matrix.updateRow_ne hi] using hA i j

theorem memLp_two_matrix_updateRow_zero
    {D : Space n → Matrix (Fin n) (Fin n) ℝ} {μ : Measure (Space n)}
    (hD : ∀ i j, MemLp (fun x => D x i j) 2 μ) (r : Fin n) :
    ∀ i j, MemLp (fun x => (D x).updateRow r 0 i j) 2 μ := by
  intro i j
  by_cases hi : i = r
  · subst i
    simpa only [Matrix.updateRow_self, Pi.zero_apply] using
      (MemLp.zero' : MemLp (fun _ : Space n => (0 : ℝ)) 2 μ)
  · simpa only [Matrix.updateRow_ne hi] using hD i j

theorem memLp_top_matrixAdjugate
    {A : Space n → Matrix (Fin n) (Fin n) ℝ} {μ : Measure (Space n)}
    (hA : ∀ i j, MemLp (fun x => A x i j) ∞ μ) (i j : Fin n) :
    MemLp (fun x => (A x).adjugate i j) ∞ μ := by
  simpa only [Matrix.adjugate_apply] using
    memLp_top_matrixDet (memLp_top_matrix_updateRow hA j (Pi.single i 1))

theorem memLp_two_adjugateDirectionalPolynomial
    {A D : Space n → Matrix (Fin n) (Fin n) ℝ} {μ : Measure (Space n)}
    (hA : ∀ i j, MemLp (fun x => A x i j) ∞ μ)
    (hD : ∀ i j, MemLp (fun x => D x i j) 2 μ) (i j : Fin n) :
    MemLp (fun x => adjugateDirectionalPolynomial (A x) (D x) i j) 2 μ := by
  simpa only [determinantDirectionalPolynomial_eq_fderiv, adjugateDirectionalPolynomial] using
    memLp_two_determinantDirectionalPolynomial (memLp_top_matrix_updateRow hA j (Pi.single i 1))
      (memLp_two_matrix_updateRow_zero hD j)

/-- Every actual adjugate entry is a determinant with a constant row, so
its genuine weak derivative follows from the polynomial determinant rule. -/
theorem hasLocalWeakCoordinateDerivative_matrixAdjugate
    {A D : Space n → Matrix (Fin n) (Fin n) ℝ} {k : Fin n}
    (hD : ∀ i j, HasLocalWeakCoordinateDerivative (fun x => A x i j) (fun x => D x i j) k)
    (hA : ∀ i j K, IsCompact K → MemLp (fun x => A x i j) ∞ (volume.restrict K))
    (hDloc : ∀ i j K, IsCompact K → MemLp (fun x => D x i j) 2 (volume.restrict K))
    (i j : Fin n) :
    HasLocalWeakCoordinateDerivative (fun x => (A x).adjugate i j)
      (fun x => adjugateDirectionalPolynomial (A x) (D x) i j) k := by
  have hrow (a b : Fin n) : HasLocalWeakCoordinateDerivative
      (fun x => (A x).updateRow j (Pi.single i 1) a b)
      (fun x => (D x).updateRow j 0 a b) k := by
    by_cases ha : a = j
    · subst a
      simpa only [Matrix.updateRow_self, Pi.zero_apply] using
        hasLocalWeakCoordinateDerivative_const ((show Fin n → ℝ from Pi.single i 1) b) k
    · simpa only [Matrix.updateRow_ne ha] using hD a b
  have hAb (a b : Fin n) (K : Set (Space n)) (hK : IsCompact K) :
      MemLp (fun x => (A x).updateRow j (Pi.single i 1) a b) ∞ (volume.restrict K) :=
    memLp_top_matrix_updateRow (fun a b => hA a b K hK) j (Pi.single i 1) a b
  have hDb (a b : Fin n) (K : Set (Space n)) (hK : IsCompact K) :
      MemLp (fun x => (D x).updateRow j 0 a b) 2 (volume.restrict K) :=
    memLp_two_matrix_updateRow_zero (fun a b => hDloc a b K hK) j a b
  simpa only [Matrix.adjugate_apply, adjugateDirectionalPolynomial] using
    hasLocalWeakCoordinateDerivative_matrixDet hrow hAb hDb

end KLS
end
