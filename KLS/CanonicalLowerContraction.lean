import KLS.CovarianceWhiteCoordinates

/-! The single-subset estimate (101)--(102), on the literal cumulants of
the current adaptive law and its actual covariance whitening. -/
open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
variable {n a b : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def canonicalLowerContraction (μ : Measure (Space n)) (a b : ℕ) (u : Space n)
    (z : Fin (n+n*n) → ℝ) (α : Fin a → Fin n) (β : Fin b → Fin n) : ℝ :=
  ∑ k, cumulantTensor (law μ (decodeState z).1 (decodeState z).2) (a+2)
    (Fin.cons (inverseSqrtDirection μ z k)
      (Fin.cons u (fun s => inverseSqrtDirection μ z (α s)))) *
    cumulantTensor (law μ (decodeState z).1 (decodeState z).2) (b+1)
      (Fin.cons (inverseSqrtDirection μ z k) (fun s => inverseSqrtDirection μ z (β s)))

omit [IsProbabilityMeasure μ] in
theorem canonicalLowerContraction_eq_evaluation (u : Space n)
    (z : Fin (n+n*n) → ℝ) (α : Fin a → Fin n) (β : Fin b → Fin n) :
    canonicalLowerContraction μ a b u z α β =
      cumulantTensor (law μ (decodeState z).1 (decodeState z).2) (b+1)
        (Fin.cons (∑ k, cumulantTensor (law μ (decodeState z).1 (decodeState z).2) (a+2)
          (Fin.cons (inverseSqrtDirection μ z k)
            (Fin.cons u (fun s => inverseSqrtDirection μ z (α s)))) •
          inverseSqrtDirection μ z k) (fun s => inverseSqrtDirection μ z (β s))) := by
  let L := (cumulantTensor (law μ (decodeState z).1 (decodeState z).2) (b+1)).curryLeft.flipMultilinear
    (fun s => inverseSqrtDirection μ z (β s))
  change _ = L (∑ k, _ • _)
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

theorem canonicalLowerContraction_square_le (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (u : Space n)
    (z : Fin (n+n*n) → ℝ) {B : ℝ}
    (hB : ∀ v : Space n, cumulantEnergy μ b v z ≤
      B * inner ℝ v (matrixAction (coordinateCovarianceMatrix μ z) v)) :
    (∑ α : Fin a → Fin n, ∑ β : Fin b → Fin n,
      canonicalLowerContraction μ a b u z α β ^ 2) ≤
      B * cumulantEnergy μ (a+1) u z := by
  let ν := law μ (decodeState z).1 (decodeState z).2
  let A := fun (α : Fin a → Fin n) (k : Fin n) => cumulantTensor ν (a+2)
    (Fin.cons (inverseSqrtDirection μ z k)
      (Fin.cons u (fun s => inverseSqrtDirection μ z (α s))))
  have hone (α : Fin a → Fin n) :
      (∑ β : Fin b → Fin n, canonicalLowerContraction μ a b u z α β ^ 2) ≤
        B * ∑ k, A α k ^ 2 := by
    have hb := hB (∑ k, A α k • inverseSqrtDirection μ z k)
    rw [covariance_norm_inverseSqrt_combination hμ hfull] at hb
    rw [cumulantEnergy_eq_whitened hμ hfull] at hb
    unfold dotProduct at hb
    simp_rw [← pow_two, whitenedCumulantTensor_eq_evaluation] at hb
    simpa only [canonicalLowerContraction_eq_evaluation, A, ν] using hb
  calc
    _ ≤ ∑ α : Fin a → Fin n, B * ∑ k, A α k ^ 2 := Finset.sum_le_sum fun α _ => hone α
    _ = B * cumulantEnergy μ (a+1) u z := by
      rw [← Finset.mul_sum, cumulantEnergy_eq_whitened hμ hfull]
      congr 1
      unfold dotProduct
      simp_rw [← pow_two, whitenedCumulantTensor_eq_evaluation]
      let := law_isProbability hμ (decodeState z).1 (decodeState z).2
      have hν : IsCompact ν.support := by dsimp [ν]; rwa [support_law hμ]
      simp_rw [A, cumulantTensor_swap_front hν]
      rw [Finset.sum_comm]
      have he := (Fin.consEquiv (fun _ : Fin (a+1) => Fin n)).sum_comp
        (fun γ => cumulantTensor ν (a+2)
          (Fin.cons u (fun s => inverseSqrtDirection μ z (γ s))) ^ 2)
      have ht (k : Fin n) (α : Fin a → Fin n) :
          (fun s => inverseSqrtDirection μ z ((Fin.consEquiv (fun _ : Fin (a+1) => Fin n)) (k, α) s)) =
            Fin.cons (inverseSqrtDirection μ z k) (fun s => inverseSqrtDirection μ z (α s)) := by
        funext s
        exact Fin.cases rfl (fun _ => rfl) s
      simpa only [Fintype.sum_prod_type, ht] using he

end KLS.AdaptiveLocalization
end
