import KLS.WeightedPerturbativeHessianHolder
import KLS.MatrixLogDetSecond

open MeasureTheory Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- A continuous positive definite matrix field is uniformly elliptic on
every compact parameter set. The constants are obtained from the actual
quadratic forms on the Euclidean unit sphere. -/
theorem compact_positive_matrix_uniform_ellipticity
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsCompact S)
    {A : X → Matrix (Fin n) (Fin n) ℝ} (hA : ContinuousOn A S)
    (hpos : ∀ x ∈ S, (A x).PosDef) :
    ∃ κ Λ : ℝ, 0 < κ ∧ 0 < Λ ∧ ∀ x ∈ S, ∀ v : Space n,
      κ * ‖v‖ ^ 2 ≤ inner ℝ v (matrixAction (A x) v) ∧
      inner ℝ v (matrixAction (A x) v) ≤ Λ * ‖v‖ ^ 2 := by
  let P := S ×ˢ sphere (0 : Space n) 1
  have hP : IsCompact P := hS.prod (isCompact_sphere _ _)
  have hAc : ContinuousOn (fun z : X × Space n => matrixAction (A z.1)) P :=
    continuous_matrixAction.comp_continuousOn
      (hA.comp continuous_fst.continuousOn (fun _ hz => hz.1))
  have hq : ContinuousOn (fun z : X × Space n => inner ℝ z.2 (matrixAction (A z.1) z.2)) P :=
    continuous_snd.continuousOn.inner (hAc.clm_apply continuous_snd.continuousOn)
  obtain ⟨κ, hκ, hlower⟩ := hP.exists_forall_le' hq (a := 0) (fun z hz => by
    apply inner_matrixAction_pos (hpos z.1 hz.1)
    intro heq
    have hh := hz.2
    rw [heq] at hh
    simp at hh)
  obtain ⟨M, hM⟩ := hS.bddAbove_image (continuous_matrixAction.comp_continuousOn hA).norm
  refine ⟨κ, max M 1, hκ, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro x hx v
  have hupper : inner ℝ v (matrixAction (A x) v) ≤ max M 1 * ‖v‖ ^ 2 := by
    have hm : ‖matrixAction (A x)‖ ≤ max M 1 := (hM (mem_image_of_mem _ hx)).trans (le_max_left _ _)
    calc
      _ ≤ ‖v‖ * ‖matrixAction (A x) v‖ := real_inner_le_norm _ _
      _ ≤ ‖v‖ * (‖matrixAction (A x)‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left ((matrixAction (A x)).le_opNorm v) (norm_nonneg _)
      _ ≤ ‖v‖ * (max M 1 * ‖v‖) := by gcongr
      _ = max M 1 * ‖v‖ ^ 2 := by ring
  refine ⟨?_, hupper⟩
  by_cases hv : v = 0
  · simp [hv]
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let z : Space n := ‖v‖⁻¹ • v
  have hz : z ∈ sphere (0 : Space n) 1 := by
    simp only [mem_sphere, dist_zero_right, z, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hnorm), inv_mul_cancel₀ hnorm.ne']
  have hlo := hlower (x, z) ⟨hx, hz⟩
  have hvz : ‖v‖ • z = v := by simp [z, smul_smul, hnorm.ne']
  have heq : inner ℝ v (matrixAction (A x) v) = ‖v‖ ^ 2 * inner ℝ z (matrixAction (A x) z) := by
    conv_lhs => rw [← hvz]
    simp only [map_smul, inner_smul_left, inner_smul_right, conj_trivial]
    ring
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_right hlo (sq_nonneg ‖v‖)]

lemma det_smul_nonsing_inv_eq_adjugate {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.det ≠ 0) : A.det • A⁻¹ = A.adjugate := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', smul_smul, mul_inv_cancel₀ hA, one_smul]

lemma posDef_adjugate {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    A.adjugate.PosDef := by
  rw [← det_smul_nonsing_inv_eq_adjugate hA.det_pos.ne']
  exact hA.inv.smul hA.det_pos

end KLS
end
