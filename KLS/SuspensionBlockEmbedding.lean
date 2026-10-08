import KLS.SuspensionLogLaplaceDerivative

/-! Actual continuous linear coordinate embeddings of the independent copies
into the suspension space. -/

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KLS

def suspensionBlockEmbedding (n N : ℕ) (i : Fin N) :
    Space n →L[ℝ] Space (suspensionDimension n N) where
  toFun x := WithLp.toLp 2 (fun k => Option.elim
    ((Fintype.equivFin (SuspensionIndex n N)).symm k) 0
    (fun ij => if ij.1 = i then x ij.2 else 0))
  map_add' x y := by
    ext k
    cases h : (Fintype.equivFin (SuspensionIndex n N)).symm k with
    | none => simp [h]
    | some ij => by_cases hi : ij.1 = i <;> simp [h, hi]
  map_smul' a x := by
    ext k
    cases h : (Fintype.equivFin (SuspensionIndex n N)).symm k with
    | none => simp [h]
    | some ij => by_cases hi : ij.1 = i <;> simp [h, hi]
  cont := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (suspensionDimension n N) => ℝ)).comp
    apply continuous_pi
    intro k
    cases h : (Fintype.equivFin (SuspensionIndex n N)).symm k with
    | none => simp only [Option.elim_none]; fun_prop
    | some ij =>
      simp only [Option.elim_some]
      by_cases hi : ij.1 = i <;> simp only [hi, ite_true, ite_false] <;> fun_prop

lemma suspensionNoiseProjection_blockEmbedding (n N : ℕ) (i : Fin N) (x : Space n) :
    suspensionNoiseProjection n N (suspensionBlockEmbedding n N i x) = 0 := by
  simp [suspensionNoiseProjection, suspensionBlockEmbedding]

lemma suspensionCopyProjection_blockEmbedding (n N : ℕ) (i j : Fin N) (x : Space n) :
    suspensionCopyProjection n N j (suspensionBlockEmbedding n N i x) =
      if j = i then x else 0 := by
  ext k
  by_cases h : j = i <;> simp [suspensionCopyProjection, suspensionBlockEmbedding, h]

lemma suspensionBlockEmbedding_basisFun (n N : ℕ) (i : Fin N) (j : Fin n) :
    suspensionBlockEmbedding n N i (EuclideanSpace.basisFun (Fin n) ℝ j) =
      EuclideanSpace.basisFun (Fin (suspensionDimension n N)) ℝ
        (Fintype.equivFin (SuspensionIndex n N) (some (i, j))) := by
  ext k
  obtain ⟨a, rfl⟩ := (Fintype.equivFin (SuspensionIndex n N)).surjective k
  cases a with
  | none => simp [suspensionBlockEmbedding]
  | some kl =>
    by_cases hi : kl.1 = i
    · by_cases hj : kl.2 = j <;> simp [suspensionBlockEmbedding, hi, hj, Prod.ext_iff]
    · simp [suspensionBlockEmbedding, hi, Prod.ext_iff]

end KLS
end
#print axioms KLS.suspensionBlockEmbedding_basisFun
