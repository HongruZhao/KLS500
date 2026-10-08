import KLS.MatrixSqrtLipschitz

/-! Local Lipschitz continuity of actual matrix inversion and inverse square
roots, in the elementwise norm. -/
open Matrix Set Filter
open scoped Topology MatrixOrder Matrix.Norms.Elementwise
noncomputable section
namespace KLS

lemma matrix_inverse_continuousAt_posDef {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ContinuousAt (fun B : Matrix (Fin n) (Fin n) ℝ => B⁻¹) A := by
  apply continuousAt_matrix_inv
  simpa only [show (Ring.inverse : ℝ → ℝ) = Inv.inv from funext Ring.inverse_eq_inv] using
    continuousAt_inv₀ hA.det_pos.ne'

lemma locallyLipschitzOn_matrix_inverse_posDef {n : ℕ} :
    LocallyLipschitzOn {A : Matrix (Fin n) (Fin n) ℝ | A.PosDef}
      (fun A => A⁻¹) := by
  intro A hA
  let R : ℝ := ‖A⁻¹‖ + 1
  let m : ℝ := (n : ℝ) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hm : 0 < m := by dsimp [m]; positivity
  have hnear : {B : Matrix (Fin n) (Fin n) ℝ | ‖B⁻¹‖ < R} ∈
      𝓝[{B | B.PosDef}] A := by
    exact (matrix_inverse_continuousAt_posDef hA).norm.continuousWithinAt
      (Iio_mem_nhds (by dsimp [R]; linarith))
  refine ⟨Real.toNNReal (m ^ 2 * R ^ 2),
    {B | B.PosDef} ∩ {B | ‖B⁻¹‖ < R},
    inter_mem self_mem_nhdsWithin hnear, LipschitzOnWith.of_dist_le' ?_⟩
  intro B hB C hC
  have hunitB : IsUnit B := (show B.PosDef from hB.1).isUnit
  have hunitC : IsUnit C := (show C.PosDef from hC.1).isUnit
  have hid : B⁻¹ - C⁻¹ = B⁻¹ * (C - B) * C⁻¹ :=
    Matrix.inv_sub_inv ⟨fun _ => hunitC, fun _ => hunitB⟩
  simp only [dist_eq_norm]
  rw [hid]
  calc
    ‖B⁻¹ * (C - B) * C⁻¹‖ ≤ m * ‖B⁻¹ * (C - B)‖ * ‖C⁻¹‖ :=
      matrix_elementwise_norm_mul_le _ _
    _ ≤ m * (m * ‖B⁻¹‖ * ‖C - B‖) * ‖C⁻¹‖ := by
      gcongr
      exact matrix_elementwise_norm_mul_le _ _
    _ ≤ m * (m * R * ‖C - B‖) * R := by gcongr; exacts [hB.2.le, hC.2.le]
    _ = m ^ 2 * R ^ 2 * ‖B - C‖ := by rw [norm_sub_rev C B]; ring

/-- The whitening map itself is locally Lipschitz on positive definite matrices. -/
theorem locallyLipschitzOn_inverseSqrtMatrix_posDef {n : ℕ} :
    LocallyLipschitzOn {A : Matrix (Fin n) (Fin n) ℝ | A.PosDef}
      inverseSqrtMatrix := by
  intro A hA
  have hroot : ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosDef → (CFC.sqrt B).PosDef := by
    intro B hB
    exact (CFC.sqrt_nonneg B).posSemidef.posDef_iff_isUnit.mpr
      ((CFC.isUnit_sqrt_iff B hB.posSemidef.nonneg).mpr hB.isUnit)
  obtain ⟨Ks, s, hs, hLs⟩ := locallyLipschitzOn_matrix_sqrt_posDef hA
  obtain ⟨Ki, t, ht, hLt⟩ := locallyLipschitzOn_matrix_inverse_posDef (hroot A hA)
  have htend : Tendsto (CFC.sqrt : Matrix (Fin n) (Fin n) ℝ → _)
      (𝓝[{B | B.PosDef}] A) (𝓝[{B | B.PosDef}] (CFC.sqrt A)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨matrix_sqrt_continuousOn_posDef A hA, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with B hB
    exact hroot B hB
  refine ⟨Ki * Ks, s ∩ CFC.sqrt ⁻¹' t, inter_mem hs (htend ht), ?_⟩
  exact hLt.comp (hLs.mono inter_subset_left) (fun B hB => hB.2)

/-- Composition with any locally Lipschitz positive-definite matrix map. -/
theorem locallyLipschitz_inverseSqrtMatrix_comp {E : Type*} [PseudoEMetricSpace E]
    {n : ℕ} {A : E → Matrix (Fin n) (Fin n) ℝ}
    (hA : LocallyLipschitz A) (hpos : ∀ x, (A x).PosDef) :
    LocallyLipschitz (fun x => inverseSqrtMatrix (A x)) := by
  intro x
  obtain ⟨KA, s, hs, hLs⟩ := hA x
  obtain ⟨Ki, t, ht, hLt⟩ := locallyLipschitzOn_inverseSqrtMatrix_posDef (hpos x)
  have htend : Tendsto A (𝓝 x) (𝓝[{B | B.PosDef}] (A x)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hA.continuous.continuousAt, Eventually.of_forall hpos⟩
  exact ⟨Ki * KA, s ∩ A ⁻¹' t, inter_mem hs (htend ht),
    hLt.comp (hLs.mono inter_subset_left) (fun _ hy => hy.2)⟩

end KLS
end
