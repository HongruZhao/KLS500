import KLS.FrameHessianAlgebra

open Matrix Set Filter Metric InnerProductSpace
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

lemma posSemidef_of_matrix_tendsto {M : ℕ → Matrix (Fin n) (Fin n) ℝ}
    {H : Matrix (Fin n) (Fin n) ℝ} (hM : ∀ j, (M j).PosSemidef)
    (hlim : Tendsto M atTop (𝓝 H)) : H.PosSemidef := by
  have hc : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A.conjTranspose) := by fun_prop
  have hh : H.IsHermitian := by
    apply tendsto_nhds_unique (hc.continuousAt.tendsto.comp hlim)
    have he : (fun j => (M j).conjTranspose) = M := funext (fun j => (hM j).isHermitian)
    change Tendsto (fun j => (M j).conjTranspose) atTop (𝓝 H)
    rw [he]
    exact hlim
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
  intro x
  have hq : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => star x ⬝ᵥ (A *ᵥ x)) := by fun_prop
  exact le_of_tendsto_of_tendsto tendsto_const_nhds (hq.continuousAt.tendsto.comp hlim)
    (Eventually.of_forall (fun j => (hM j).dotProduct_mulVec_nonneg x))

lemma matrixAction_sub_eq (A B : Matrix (Fin n) (Fin n) ℝ) :
    matrixAction (A - B) = matrixAction A - matrixAction B := by
  apply ContinuousLinearMap.ext
  intro x
  exact matrixAction_sub_matrices A B x

end KLS
end
