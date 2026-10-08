import KLS.TranslatedHessianDifferenceQuotient

open MeasureTheory Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

def matrixQuadraticFormCLM (v : Space n) : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  ({ toFun := fun A => inner ℝ v (matrixAction A v)
     map_add' := fun A B => by rw [matrixAction_add_matrices, inner_add_right]
     map_smul' := fun r A => by
       rw [matrixAction_smul_scalar, inner_smul_right]
       rfl } : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ).toContinuousLinearMap

@[simp] lemma matrixQuadraticFormCLM_apply (v : Space n) (A : Matrix (Fin n) (Fin n) ℝ) :
    matrixQuadraticFormCLM v A = inner ℝ v (matrixAction A v) := rfl

lemma averagedCofactor_quadratic_form (A B : Matrix (Fin n) (Fin n) ℝ) (v : Space n) :
    inner ℝ v (matrixAction (averagedCofactor A B) v) =
      ∫ t in (0 : ℝ)..1, inner ℝ v (matrixAction (matrixChord A B t).adjugate v) := by
  exact ((matrixQuadraticFormCLM v).intervalIntegral_comp_comm
    ((continuous_adjugate_matrixChord A B).intervalIntegrable (0 : ℝ) 1)).symm

def matrixEntryCLM (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  ({ toFun := fun A => A i j
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ).toContinuousLinearMap

lemma averagedCofactor_entry (A B : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    averagedCofactor A B i j = ∫ t in (0 : ℝ)..1, (matrixChord A B t).adjugate i j := by
  have hint : IntervalIntegrable (fun t => (matrixChord A B t).adjugate) volume 0 1 :=
    (continuous_adjugate_matrixChord A B).intervalIntegrable (0 : ℝ) 1
  exact ((matrixEntryCLM i j).intervalIntegral_comp_comm hint).symm

lemma averagedCofactor_isSymm {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hB : B.PosDef) : (averagedCofactor A B).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  rw [averagedCofactor_entry, averagedCofactor_entry]
  apply intervalIntegral.integral_congr
  intro t ht
  exact (posDef_adjugate (matrixChord_posDef hA hB
    (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht))).isHermitian.isSymm.apply i j

/-- The averaged cofactors of all pairs in a compact positive matrix set
are uniformly elliptic. Positivity and both constants are proved before
any choice of spatial translation or difference-quotient step. -/
theorem averagedCofactor_uniform_ellipticity_on_compact
    {K : Set (Matrix (Fin n) (Fin n) ℝ)} (hK : IsCompact K)
    (hpos : ∀ A ∈ K, A.PosDef) :
    ∃ κ Λ : ℝ, 0 < κ ∧ 0 < Λ ∧
      ∀ A ∈ K, ∀ B ∈ K, ∀ v : Space n,
        κ * ‖v‖ ^ 2 ≤ inner ℝ v (matrixAction (averagedCofactor A B) v) ∧
        inner ℝ v (matrixAction (averagedCofactor A B) v) ≤ Λ * ‖v‖ ^ 2 := by
  let S := (K ×ˢ K) ×ˢ Icc (0 : ℝ) 1
  let F := fun z : (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) × ℝ =>
    (matrixChord z.1.1 z.1.2 z.2).adjugate
  have hF : Continuous F := by
    apply MatrixCalculus.contDiff_adjugate.continuous.comp
    unfold matrixChord
    fun_prop
  have hp : ∀ z ∈ S, (F z).PosDef := by
    intro z hz
    exact posDef_adjugate (matrixChord_posDef (hpos z.1.1 hz.1.1) (hpos z.1.2 hz.1.2) hz.2)
  obtain ⟨κ, Λ, hκ, hΛ, hell⟩ := compact_positive_matrix_uniform_ellipticity
    ((hK.prod hK).prod isCompact_Icc) hF.continuousOn hp
  refine ⟨κ, Λ, hκ, hΛ, ?_⟩
  intro A hA B hB v
  have hint : IntervalIntegrable (fun t => inner ℝ v (matrixAction (matrixChord A B t).adjugate v)) volume 0 1 :=
    ((matrixQuadraticFormCLM v).continuous.comp (continuous_adjugate_matrixChord A B)).intervalIntegrable _ _
  rw [averagedCofactor_quadratic_form]
  constructor
  · have hh := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => κ * ‖v‖ ^ 2) volume 0 1) hint
      (fun t ht => (hell ((A, B), t) ⟨⟨hA, hB⟩, ht⟩ v).1)
    simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using hh
  · have hh := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hint
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Λ * ‖v‖ ^ 2) volume 0 1)
      (fun t ht => (hell ((A, B), t) ⟨⟨hA, hB⟩, ht⟩ v).2)
    simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using hh

/-- Applied to the actual continuous Hessian field, the constants are
uniform over every pair of points of the compact spatial set. -/
theorem averagedCofactor_uniform_ellipticity_of_continuous_hessian
    {u : Space n → ℝ} {S : Set (Space n)} (hS : IsCompact S)
    (hH : ContinuousOn (coordinateHessian u) S)
    (hpos : ∀ x ∈ S, (coordinateHessian u x).PosDef) :
    ∃ κ Λ : ℝ, 0 < κ ∧ 0 < Λ ∧ ∀ x ∈ S, ∀ y ∈ S, ∀ v : Space n,
      κ * ‖v‖ ^ 2 ≤ inner ℝ v
        (matrixAction (averagedCofactor (coordinateHessian u x) (coordinateHessian u y)) v) ∧
      inner ℝ v (matrixAction (averagedCofactor (coordinateHessian u x) (coordinateHessian u y)) v) ≤
        Λ * ‖v‖ ^ 2 := by
  obtain ⟨κ, Λ, hκ, hΛ, hb⟩ := averagedCofactor_uniform_ellipticity_on_compact
    (hS.image_of_continuousOn hH) (by rintro _ ⟨x, hx, rfl⟩; exact hpos x hx)
  exact ⟨κ, Λ, hκ, hΛ, fun x hx y hy v => hb _ (mem_image_of_mem _ hx) _ (mem_image_of_mem _ hy) v⟩

end KLS
end
