import KLS.WeightedTiltTaylorTensor

open InnerProductSpace
noncomputable section
namespace KLS

/-- The actual scalar coordinate parametrization of Euclidean dimension one. -/
def scalarAxisEquiv : ℝ ≃L[ℝ] Space 1 :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun s => s • EuclideanSpace.single (0 : Fin 1) 1
      invFun := fun x => x 0
      left_inv := by intro s; simp
      right_inv := by
        intro x
        ext i
        have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
        rw [hi]
        simp
      map_add' := by intro s t; rw [add_smul]
      map_smul' := by intro s t; simp [mul_smul] }

lemma scalarAxisEquiv_apply (s : ℝ) :
    scalarAxisEquiv s = s • EuclideanSpace.single (0 : Fin 1) 1 := rfl

/-- Scalar iterated derivatives along the sole coordinate agree with the
literal Fréchet tensor evaluated on that coordinate in every slot. -/
theorem iteratedDeriv_scalarAxis_eq_coordinate_jet (A : Space 1 → ℝ) (m : ℕ) :
    iteratedDeriv m (fun s : ℝ => A (s • EuclideanSpace.single (0 : Fin 1) 1)) 0 =
      iteratedFDeriv ℝ m A 0 (fun _ => EuclideanSpace.single (0 : Fin 1) 1) := by
  have hh := scalarAxisEquiv.iteratedFDerivWithin_comp_right A uniqueDiffOn_univ
    (x := (0 : ℝ)) (Set.mem_univ _) m
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ, map_zero] at hh
  have he := congrArg (fun M : ContinuousMultilinearMap ℝ (fun _ : Fin m => ℝ) ℝ =>
    M (fun _ => 1)) hh
  simpa only [iteratedDeriv_eq_iteratedFDeriv, Function.comp_def, scalarAxisEquiv_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe, one_smul] using he

end KLS
end
