import KLS.HarmonicBernsteinPointwise

open MeasureTheory InnerProductSpace Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

def harmonicBallWeight (c : Space n) (R : ℝ) : Space n → ℝ :=
  centeredQuadratic ((-2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) c 0 (R ^ 2)

lemma harmonicBallWeight_apply (c : Space n) (R : ℝ) (x : Space n) :
    harmonicBallWeight c R x = R ^ 2 - dist x c ^ 2 := by
  simp only [harmonicBallWeight, centeredQuadratic, inner_zero_left, add_zero,
    matrixAction_smul_scalar, matrixAction_one_apply, inner_smul_right,
    real_inner_self_eq_norm_sq, dist_eq_norm]
  ring

lemma contDiff_harmonicBallWeight (c : Space n) (R : ℝ) {m : WithTop ℕ∞} :
    ContDiff ℝ m (harmonicBallWeight c R) :=
  (contDiff_centeredQuadratic _ _ _ _).of_le le_top

lemma laplacian_harmonicBallWeight (c : Space n) (R : ℝ) (x : Space n) :
    coordinateLaplacian (harmonicBallWeight c R) x = -2 * n := by
  unfold coordinateLaplacian harmonicBallWeight
  simp_rw [coordinateHessian_centeredQuadratic_of_isSymm (Matrix.isSymm_one.smul (-2 : ℝ))]
  simp [Matrix.smul_apply, smul_eq_mul, mul_comm]

lemma harmonicGradientSquare_harmonicBallWeight (c : Space n) (R : ℝ) (x : Space n) :
    harmonicGradientSquare (harmonicBallWeight c R) x = 4 * dist x c ^ 2 := by
  rw [harmonicGradientSquare_eq_norm_gradient_sq]
  unfold harmonicBallWeight
  rw [gradient_centeredQuadratic_of_isSymm (Matrix.isSymm_one.smul (-2 : ℝ))]
  simp only [zero_add, matrixAction_smul_scalar, matrixAction_one_apply, norm_smul,
    Real.norm_eq_abs, mul_pow, dist_eq_norm]
  norm_num

/-- The actual Bernstein maximum argument controls every first derivative of
a harmonic function by its supremum on a ball. The weight is a concrete
quadratic, so no derivative-bound premise is imposed on a cutoff. -/
theorem harmonicBernsteinAux_le_on_closedBall {f : Space n → ℝ}
    (hf : ContDiff ℝ 3 f) {c : Space n} {R B : ℝ} (hR : 0 < R)
    (hharm : ∀ x ∈ ball c R, coordinateLaplacian f x = 0)
    (hbound : ∀ x ∈ closedBall c R, f x ^ 2 ≤ B) (i : Fin n) :
    ∀ x ∈ closedBall c R,
      harmonicBernsteinAux (harmonicBallWeight c R) (coordinateDerivative f i) f
        ((30 + 2 * n) * R ^ 2) x ≤ ((30 + 2 * n) * R ^ 2) * B := by
  let η := harmonicBallWeight c R
  let u := coordinateDerivative f i
  let A : ℝ := (30 + 2 * n) * R ^ 2
  let F := harmonicBernsteinAux η u f A
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hη : ContDiff ℝ 2 η := contDiff_harmonicBallWeight c R
  have hu : ContDiff ℝ 2 u := contDiff_coordinateDerivative hf (by norm_num) i
  have hF : ContDiff ℝ 2 F := contDiff_harmonicBernsteinAux hη hu hf2 A
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  intro z hz
  change F z ≤ A * B
  by_contra! hbad
  obtain ⟨q, hq, hmax⟩ := (isCompact_closedBall c R).exists_isMaxOn ⟨z, hz⟩ hF.continuous.continuousOn
  have hqbad : A * B < F q := hbad.trans_le (hmax hz)
  have hqint : q ∈ ball c R := by
    have hd : dist q c ≤ R := hq
    by_contra hn
    have he : dist q c = R := le_antisymm hd (le_of_not_gt hn)
    have hηq : η q = 0 := by simp [η, harmonicBallWeight_apply, he]
    have hFq : F q = A * f q ^ 2 := by simp [F, harmonicBernsteinAux, hηq]
    rw [hFq] at hqbad
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_left (hbound q hq) hA0)) hqbad
  have hmaxlocal : IsLocalMax F q := hmax.isLocalMax
    (mem_of_superset (isOpen_ball.mem_nhds hqint) ball_subset_closedBall)
  have hnonpos := coordinateLaplacian_nonpos_of_isLocalMax hF hmaxlocal
  have hηupper : η q ≤ R ^ 2 := by
    dsimp only [η]
    rw [harmonicBallWeight_apply]
    exact sub_le_self _ (sq_nonneg _)
  have he : harmonicGradientSquare η q ≤ 4 * R ^ 2 := by
    dsimp only [η]
    rw [harmonicGradientSquare_harmonicBallWeight]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (dist_nonneg : 0 ≤ dist q c) (show dist q c ≤ R from hq) 2) (by norm_num)
  have hlower := laplacian_harmonicBernsteinAux_lower hη hu hf2 R q hηupper
    (laplacian_harmonicBallWeight c R q) he
    (coordinateLaplacian_derivative_eq_zero_on hf isOpen_ball hharm i hqint)
    (hharm q hqint) (coordinateDerivative_sq_le_harmonicGradientSquare f q i)
  change 4 * R ^ 2 * u q ^ 2 ≤ coordinateLaplacian F q at hlower
  have huq : u q ^ 2 = 0 := by nlinarith [sq_nonneg (u q), sq_pos_of_pos hR]
  have hFq : F q = A * f q ^ 2 := by simp [F, harmonicBernsteinAux, huq]
  rw [hFq] at hqbad
  exact (not_lt_of_ge (mul_le_mul_of_nonneg_left (hbound q hq) hA0)) hqbad

/-- Explicit dimension-dependent interior bound for each actual coordinate
derivative of a classical harmonic function. -/
theorem coordinateDerivative_sq_le_of_harmonic_on_ball {f : Space n → ℝ}
    (hf : ContDiff ℝ 3 f) {c : Space n} {R B : ℝ} (hR : 0 < R)
    (hharm : ∀ x ∈ ball c R, coordinateLaplacian f x = 0)
    (hbound : ∀ x ∈ closedBall c R, f x ^ 2 ≤ B)
    (i : Fin n) {x : Space n} (hx : x ∈ closedBall c (R / 2)) :
    coordinateDerivative f i x ^ 2 ≤ (120 + 8 * n) * B / R ^ 2 := by
  have hxR : x ∈ closedBall c R := closedBall_subset_closedBall (by linarith) hx
  have hh := harmonicBernsteinAux_le_on_closedBall hf hR hharm hbound i x hxR
  have hd : dist x c ^ 2 ≤ (R / 2) ^ 2 :=
    pow_le_pow_left₀ dist_nonneg (show dist x c ≤ R / 2 from hx) 2
  have hη : R ^ 2 / 2 ≤ harmonicBallWeight c R x := by rw [harmonicBallWeight_apply]; nlinarith
  have hη0 : 0 ≤ harmonicBallWeight c R x := (by positivity : 0 ≤ R ^ 2 / 2).trans hη
  have hηsq : R ^ 4 / 4 ≤ harmonicBallWeight c R x ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hηsq (sq_nonneg (coordinateDerivative f i x))
  have hA0 : 0 ≤ ((30 + 2 * n : ℝ) * R ^ 2) * f x ^ 2 := by positivity
  unfold harmonicBernsteinAux at hh
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  have hscale : 0 < R ^ 2 := sq_pos_of_pos hR
  nlinarith

end KLS
end
