import KLS.LocalC2DensityCalculus

open MeasureTheory Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

lemma norm_matrixChord_le {A B : Matrix (Fin n) (Fin n) ℝ} {R t : ℝ}
    (hA : ‖A‖ ≤ R) (hB : ‖B‖ ≤ R) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖matrixChord A B t‖ ≤ R := by
  rw [matrixChord_eq]
  calc
    _ ≤ ‖(1 - t) • A‖ + ‖t • B‖ := norm_add_le _ _
    _ = (1 - t) * ‖A‖ + t * ‖B‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
    _ ≤ (1 - t) * R + t * R := add_le_add
      (mul_le_mul_of_nonneg_left hA (sub_nonneg.mpr ht.2)) (mul_le_mul_of_nonneg_left hB ht.1)
    _ = R := by ring

lemma norm_matrixChord_sub_le (A B C D : Matrix (Fin n) (Fin n) ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖matrixChord A B t - matrixChord C D t‖ ≤ ‖A - C‖ + ‖B - D‖ := by
  have heq : matrixChord A B t - matrixChord C D t = matrixChord (A - C) (B - D) t := by
    simp only [matrixChord_eq, smul_sub]
    abel
  rw [heq]
  exact norm_matrixChord_le (le_add_of_nonneg_right (norm_nonneg _))
    (le_add_of_nonneg_left (norm_nonneg _)) ht

/-- Adjugation is polynomial, so the actual averaged cofactor is
Lipschitz in its two matrix endpoints on every bounded matrix ball. -/
theorem exists_lipschitz_bound_averagedCofactor (R : ℝ) :
    ∃ L : ℝ≥0, ∀ A B C D : Matrix (Fin n) (Fin n) ℝ,
      ‖A‖ ≤ R → ‖B‖ ≤ R → ‖C‖ ≤ R → ‖D‖ ≤ R →
      ‖averagedCofactor A B - averagedCofactor C D‖ ≤ L * (‖A - C‖ + ‖B - D‖) := by
  obtain ⟨L, hL⟩ := (MatrixCalculus.contDiff_adjugate.contDiffOn
    (s := closedBall (0 : Matrix (Fin n) (Fin n) ℝ) R)).exists_lipschitzOnWith
      (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  refine ⟨L, ?_⟩
  intro A B C D hA hB hC hD
  have hintAB : IntervalIntegrable (fun t => (matrixChord A B t).adjugate) volume 0 1 :=
    (continuous_adjugate_matrixChord A B).intervalIntegrable _ _
  have hintCD : IntervalIntegrable (fun t => (matrixChord C D t).adjugate) volume 0 1 :=
    (continuous_adjugate_matrixChord C D).intervalIntegrable _ _
  unfold averagedCofactor
  rw [← intervalIntegral.integral_sub hintAB hintCD]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 1) (C := (L : ℝ) * (‖A - C‖ + ‖B - D‖)) (fun t ht => by
      have htI : t ∈ Ioc (0 : ℝ) 1 := by
        simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨htI.1.le, htI.2⟩
      have hAB : matrixChord A B t ∈ closedBall (0 : Matrix (Fin n) (Fin n) ℝ) R :=
        mem_closedBall_zero_iff.mpr (norm_matrixChord_le hA hB ht')
      have hCD : matrixChord C D t ∈ closedBall (0 : Matrix (Fin n) (Fin n) ℝ) R :=
        mem_closedBall_zero_iff.mpr (norm_matrixChord_le hC hD ht')
      have hbound := hL.dist_le_mul _ hAB _ hCD
      rw [dist_eq_norm, dist_eq_norm] at hbound
      exact hbound.trans (mul_le_mul_of_nonneg_left (norm_matrixChord_sub_le A B C D ht') L.coe_nonneg))
  simpa only [sub_zero, abs_one, mul_one] using hh

/-- A Holder Hessian gives Holder coefficients for all translated
quotient equations, with one constant independent of the translation. -/
theorem averagedCofactor_holder_of_bounded_holder_field
    {H : Space n → Matrix (Fin n) (Fin n) ℝ} {S : Set (Space n)} {R M γ : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ x ∈ S, ‖H x‖ ≤ R)
    (hholder : ∀ x ∈ S, ∀ y ∈ S, ‖H x - H y‖ ≤ M * ‖x - y‖ ^ γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a x y : Space n),
      x ∈ S → x + a ∈ S → y ∈ S → y + a ∈ S →
      ‖averagedCofactor (H x) (H (x + a)) - averagedCofactor (H y) (H (y + a))‖ ≤
        C * ‖x - y‖ ^ γ := by
  obtain ⟨L, hL⟩ := exists_lipschitz_bound_averagedCofactor (n := n) R
  refine ⟨2 * L * M, by positivity, ?_⟩
  intro a x y hx hxa hy hya
  have h0 := hholder x hx y hy
  have h1 := hholder (x + a) hxa (y + a) hya
  rw [add_sub_add_right_eq_sub] at h1
  calc
    _ ≤ L * (‖H x - H y‖ + ‖H (x + a) - H (y + a)‖) :=
      hL _ _ _ _ (hbound x hx) (hbound _ hxa) (hbound y hy) (hbound _ hya)
    _ ≤ L * (M * ‖x - y‖ ^ γ + M * ‖x - y‖ ^ γ) :=
      mul_le_mul_of_nonneg_left (add_le_add h0 h1) L.coe_nonneg
    _ = (2 * L * M) * ‖x - y‖ ^ γ := by ring

end KLS
end
