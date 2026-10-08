import KLS.LocalWeakFiniteProduct

open MeasureTheory Set Filter Matrix
open scoped BigOperators ContDiff Topology ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

theorem memLp_top_matrixMul
    {A B : Space n → Matrix (Fin n) (Fin n) ℝ} {μ : Measure (Space n)}
    (hA : ∀ i j, MemLp (fun x => A x i j) ∞ μ)
    (hB : ∀ i j, MemLp (fun x => B x i j) ∞ μ) (i j : Fin n) :
    MemLp (fun x => (A x * B x) i j) ∞ μ := by
  simp only [Matrix.mul_apply]
  apply memLp_finsetSum
  intro k _
  exact (hA i k).mul (hB k j)

theorem memLp_two_matrixMul_left
    {A B : Space n → Matrix (Fin n) (Fin n) ℝ} {μ : Measure (Space n)}
    (hA : ∀ i j, MemLp (fun x => A x i j) ∞ μ)
    (hB : ∀ i j, MemLp (fun x => B x i j) 2 μ) (i j : Fin n) :
    MemLp (fun x => (A x * B x) i j) 2 μ := by
  simp only [Matrix.mul_apply]
  apply memLp_finsetSum
  intro k _
  exact (hA i k).mul (hB k j)

theorem memLp_two_matrixMul_right
    {A B : Space n → Matrix (Fin n) (Fin n) ℝ} {μ : Measure (Space n)}
    (hA : ∀ i j, MemLp (fun x => A x i j) 2 μ)
    (hB : ∀ i j, MemLp (fun x => B x i j) ∞ μ) (i j : Fin n) :
    MemLp (fun x => (A x * B x) i j) 2 μ := by
  simp only [Matrix.mul_apply]
  apply memLp_finsetSum
  intro k _
  have h : MemLp (fun x => B x k j * A x i k) 2 μ := (hB k j).mul (hA i k)
  simpa only [mul_comm] using h

/-- The noncommutative matrix product order is retained in weak calculus. -/
theorem hasLocalWeakCoordinateDerivative_matrixMul
    {A B DA DB : Space n → Matrix (Fin n) (Fin n) ℝ} {k : Fin n}
    (hDA : ∀ i j, HasLocalWeakCoordinateDerivative (fun x => A x i j) (fun x => DA x i j) k)
    (hDB : ∀ i j, HasLocalWeakCoordinateDerivative (fun x => B x i j) (fun x => DB x i j) k)
    (hA : ∀ i j K, IsCompact K → MemLp (fun x => A x i j) ∞ (volume.restrict K))
    (hB : ∀ i j K, IsCompact K → MemLp (fun x => B x i j) ∞ (volume.restrict K))
    (hDAloc : ∀ i j K, IsCompact K → MemLp (fun x => DA x i j) 2 (volume.restrict K))
    (hDBloc : ∀ i j K, IsCompact K → MemLp (fun x => DB x i j) 2 (volume.restrict K))
    (i j : Fin n) :
    HasLocalWeakCoordinateDerivative (fun x => (A x * B x) i j)
      (fun x => (DA x * B x + A x * DB x) i j) k := by
  have hp (a : Fin n) := (hDA i a).mul (hDB a j)
    (memLp_two_on_compacts_of_top (hA i a)) (memLp_two_on_compacts_of_top (hB a j))
    (hDAloc i a) (hDBloc a j)
  have hP (a : Fin n) : LocallyIntegrable (fun x => A x i a * B x a j) volume := by
    apply locallyIntegrable_of_memLp_two_on_compacts
    apply memLp_two_on_compacts_of_top
    exact fun K hK => (hA i a K hK).mul (hB a j K hK)
  have hQ (a : Fin n) :
      LocallyIntegrable (fun x => DA x i a * B x a j + A x i a * DB x a j) volume := by
    apply locallyIntegrable_of_memLp_two_on_compacts
    intro K hK
    have ha : MemLp (fun x => DA x i a * B x a j) 2 (volume.restrict K) := by
      have hb : MemLp (fun x => B x a j * DA x i a) 2 (volume.restrict K) :=
        (hB a j K hK).mul (hDAloc i a K hK)
      simpa only [mul_comm] using hb
    exact ha.add ((hA i a K hK).mul (hDBloc a j K hK))
  have hs := hasLocalWeakCoordinateDerivative_finset_sum Finset.univ
    (fun a _ => hp a) (fun a _ => hP a) (fun a _ => hQ a)
  simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib] using hs

end KLS
end
