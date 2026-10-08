import KLS.QuadraticFrameReconstruction

open Matrix Set Filter Metric InnerProductSpace
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

lemma inner_inverse_transpose_frame
    {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.det ≠ 0) (p y : Space n) :
    inner ℝ (matrixAction T⁻¹.transpose p) (matrixAction T y) = inner ℝ p y := by
  rw [inner_matrixAction_transpose, Matrix.transpose_transpose, matrixAction_inverse_cancel hT]

lemma iteration_physical_successor
    {d₀ : NormalizedWeightedMomentData n 1 1} {ρ Q β : ℝ} {j : ℕ}
    {s : WeightedIterationState d₀ ρ Q β j}
    {t : WeightedIterationState d₀ ρ Q β (j + 1)}
    (l : WeightedIterationLink s t) (y : Space n) :
    (ρ / 2) ^ (j + 1) • matrixAction t.frame y =
      (ρ / 2) ^ j • matrixAction s.frame ((ρ / 2) • matrixAction (inverseSqrtMatrix l.A) y) := by
  rw [l.frame_eq, MomentMap.matrixAction_mul_apply, map_smul, smul_smul, pow_succ]

lemma iteration_local_reconstruction
    {d₀ : NormalizedWeightedMomentData n 1 1} {ρ Q β : ℝ} {j : ℕ}
    {s : WeightedIterationState d₀ ρ Q β j}
    {t : WeightedIterationState d₀ ρ Q β (j + 1)}
    (l : WeightedIterationLink s t) (hρ : ρ ≠ 0) (y : Space n) :
    s.data.u ((ρ / 2) • matrixAction (inverseSqrtMatrix l.A) y) =
      l.a + (ρ / 2) * inner ℝ l.p (matrixAction (inverseSqrtMatrix l.A) y) +
        (ρ / 2) ^ 2 * t.data.u y := by
  have hh := quadratic_rescaling_reconstruction s.data.u 0 l.p l.a (r := ρ / 2)
    (div_ne_zero hρ (by norm_num)) (matrixAction (inverseSqrtMatrix l.A) y)
  simpa only [zero_add, l.potential_eq, Function.comp_apply] using hh

/-- Exact reconstruction of the actual original potential from every
normalized iterate. The initial-state equality is essential here. -/
theorem iteration_affine_reconstruction
    {d₀ : NormalizedWeightedMomentData n 1 1} {ρ Q β : ℝ}
    (s : (j : ℕ) → WeightedIterationState d₀ ρ Q β j)
    (links : ∀ j, WeightedIterationLink (s j) (s (j + 1)))
    (hstart : s 0 = initialWeightedIterationState d₀ ρ Q β) (hρ : ρ ≠ 0) :
    ∀ (j : ℕ) (y : Space n),
      d₀.u ((ρ / 2) ^ j • matrixAction (s j).frame y) =
        iterationConstant s links j +
          inner ℝ (iterationSlope s links j) ((ρ / 2) ^ j • matrixAction (s j).frame y) +
          (ρ / 2) ^ (2 * j) * ((s j).data.u y - (s j).data.c) := by
  intro j
  induction j with
  | zero =>
      intro y
      simp only [hstart, initialWeightedIterationState, iterationSlope, iterationConstant,
        pow_zero, Nat.mul_zero, one_smul, matrixAction_one_apply, inner_zero_left, one_mul]
      ring
  | succ j ih =>
      intro y
      have hc := (s (j + 1)).constant_eq (Nat.succ_ne_zero j)
      rw [iteration_physical_successor (links j), ih,
        iteration_local_reconstruction (links j) hρ, iterationConstant, iterationSlope, hc]
      simp only [inner_add_left, real_inner_smul_left, inner_smul_right, map_smul]
      rw [inner_inverse_transpose_frame (iteration_frame_det_ne_zero (s j))]
      have he : (ρ / 2) ^ (2 * (j + 1)) = (ρ / 2) ^ (2 * j) * (ρ / 2) ^ 2 := by
        rw [Nat.mul_add, Nat.mul_one, pow_add]
      have hp : (ρ / 2) ^ (2 * j) = ((ρ / 2) ^ j) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
      rw [he, hp]
      ring

/-- The finite Hessian, slope and constant describe the actual approximation
error of the original potential, rather than just a formal coefficient sequence. -/
theorem iteration_quadratic_error_identity
    {d₀ : NormalizedWeightedMomentData n 1 1} {ρ Q β : ℝ}
    (s : (j : ℕ) → WeightedIterationState d₀ ρ Q β j)
    (links : ∀ j, WeightedIterationLink (s j) (s (j + 1)))
    (hstart : s 0 = initialWeightedIterationState d₀ ρ Q β) (hρ : ρ ≠ 0)
    (j : ℕ) (y : Space n) :
    d₀.u ((ρ / 2) ^ j • matrixAction (s j).frame y) -
        centeredQuadratic (frameHessian (s j).frame) 0
          (iterationSlope s links j) (iterationConstant s links j)
          ((ρ / 2) ^ j • matrixAction (s j).frame y) =
      (ρ / 2) ^ (2 * j) * ((s j).data.u y -
        centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (s j).data.c y) := by
  rw [iteration_affine_reconstruction s links hstart hρ]
  have hq := centeredQuadratic_frame_scaled (iteration_frame_det_ne_zero (s j))
    (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 ((ρ / 2) ^ j) y
  simp only [mul_one, map_zero, smul_zero, mul_zero] at hq
  change centeredQuadratic (frameHessian (s j).frame) 0 0 0
    ((ρ / 2) ^ j • matrixAction (s j).frame y) =
      ((ρ / 2) ^ j) ^ 2 * centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0 y at hq
  simp only [centeredQuadratic, sub_zero, inner_zero_left, zero_add] at hq ⊢
  rw [hq, ← pow_mul, Nat.mul_comm j 2]
  ring

end KLS
end
