import KLS.CompactPositiveMatrixField

open MeasureTheory Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

def matrixChord (A B : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ := A + t • (B - A)

lemma matrixChord_eq (A B : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    matrixChord A B t = (1 - t) • A + t • B := by
  simp only [matrixChord, smul_sub, sub_smul, one_smul]
  abel

lemma matrixChord_posDef {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (matrixChord A B t).PosDef := by
  by_cases htone : t = 1
  · subst t
    simpa only [matrixChord, one_smul, add_sub_cancel] using hB
  rw [matrixChord_eq]
  exact (hA.smul (sub_pos.mpr (lt_of_le_of_ne ht.2 htone))).add_posSemidef
    (hB.posSemidef.smul ht.1)

lemma continuous_matrixChord (A B : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (matrixChord A B) := by unfold matrixChord; fun_prop

lemma hasDerivAt_matrixChord (A B : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (matrixChord A B) (B - A) t := by
  change HasDerivAt (fun s : ℝ => A + s • (B - A)) (B - A) t
  simpa only [one_smul, id_eq] using
    ((hasDerivAt_id t).smul_const (B - A)).const_add A

def matrixTraceRightCLM (B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  ({ toFun := fun A => (A * B).trace
     map_add' := fun A C => by simp only [Matrix.add_mul, Matrix.trace_add]
     map_smul' := fun r A => by simp only [Matrix.smul_mul, Matrix.trace_smul, RingHom.id_apply] } :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ).toContinuousLinearMap

@[simp] lemma matrixTraceRightCLM_apply (A B : Matrix (Fin n) (Fin n) ℝ) :
    matrixTraceRightCLM B A = (A * B).trace := rfl

/-- The cofactor average is an actual matrix-valued integral along the
segment joining the two actual Hessian values. -/
def averagedCofactor (A B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∫ t in (0 : ℝ)..1, (matrixChord A B t).adjugate

lemma continuous_adjugate_matrixChord (A B : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun t => (matrixChord A B t).adjugate) :=
  MatrixCalculus.contDiff_adjugate.continuous.comp (continuous_matrixChord A B)

lemma hasDerivAt_det_matrixChord {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => (matrixChord A B s).det)
      ((matrixChord A B t).adjugate * (B - A)).trace t := by
  have hM := matrixChord_posDef hA hB ht
  have hdet := (MatrixCalculus.contDiff_det.differentiable (by simp)
    (matrixChord A B t)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_matrixChord A B t)
  rw [MatrixCalculus.fderiv_det_apply _ _ hM.det_pos.ne'] at hdet
  rw [← det_smul_nonsing_inv_eq_adjugate hM.det_pos.ne', Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul]
  exact hdet

/-- Exact nonlinear determinant difference; the right side is linear in
the Hessian difference, with a coefficient constructed by integration. -/
theorem determinant_chord_identity {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hB : B.PosDef) :
    B.det - A.det = (averagedCofactor A B * (B - A)).trace := by
  have hint : IntervalIntegrable (fun t => (matrixChord A B t).adjugate) volume 0 1 :=
    (continuous_adjugate_matrixChord A B).intervalIntegrable (0 : ℝ) 1
  have htint : IntervalIntegrable (fun t => matrixTraceRightCLM (B - A) ((matrixChord A B t).adjugate)) volume 0 1 :=
    ((matrixTraceRightCLM (B - A)).continuous.comp
    (continuous_adjugate_matrixChord A B)).intervalIntegrable (0 : ℝ) 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_det_matrixChord hA hB (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht)) htint
  have hcomm := (matrixTraceRightCLM (B - A)).intervalIntegral_comp_comm hint
  simpa only [matrixTraceRightCLM_apply, averagedCofactor, matrixChord,
    zero_smul, add_zero, one_smul, add_sub_cancel] using hFTC.symm.trans hcomm

end KLS
end
