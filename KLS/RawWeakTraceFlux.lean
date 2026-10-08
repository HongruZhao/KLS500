import KLS.RawWeakTraceContractions

open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Contract the actual matrix-flux ordering against the raw derivative
of the compact sandwich test. Adjacent tensor symmetry is explicit. -/
theorem raw_weak_hessian_matrixFlux_trace
    (H B : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hfirst : ∀ i j k, T i j k = T j i k)
    (hlast : ∀ i j k, T i j k = T i k j)
    (χ : ℝ) (dχ : Fin n → ℝ) :
    (∑ i, ∑ j, ∑ a, (H⁻¹ * T i) a j *
      (dχ a * (B * H * B) i j + χ * (B * T a * B) i j)) =
      (∑ a, ∑ b, H⁻¹ a b * dχ a * (B * H * B * T b).trace) +
        χ * rawHessianTraceGradientTerm H B T := by
  have he : (∑ i, ∑ j, ∑ a, (H⁻¹ * T i) a j *
      (dχ a * (B * H * B) i j + χ * (B * T a * B) i j)) =
      ∑ i, ∑ j, ∑ a, ∑ b, H⁻¹ a b *
        (dχ a * (B * H * B) i j + χ * (B * T a * B) i j) * T b i j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.mul_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    rw [hfirst i b j]
    ring
  rw [he]
  exact raw_weak_hessian_trace_left H B T
    (fun b => Matrix.IsSymm.ext fun i j => (hlast b i j).symm) χ dχ

/-- Symmetry of the actual inverse Hessian converts the boundary contraction
into one half of the raw trace-square weak-gradient pairing. -/
theorem raw_weak_hessian_trace_boundary_half
    (H B : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hJ : H⁻¹.IsSymm) (dχ : Fin n → ℝ) :
    (∑ a, ∑ b, H⁻¹ a b * dχ a * (B * H * B * T b).trace) =
      (1 / 2 : ℝ) * (∑ i, ∑ j, H⁻¹ i j *
        (2 * (B * H * B * T i).trace) * dχ j) := by
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hJ.apply j i]
  ring

end KLS
end
