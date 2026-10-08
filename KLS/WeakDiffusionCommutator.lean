import KLS.WeakWeightedIntegration

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter Matrix
open scoped BigOperators ContDiff Topology ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

theorem locallyLipschitz_weightedDiffusion
    {φ g : Space n → ℝ} (hG : LocallyLipschitz (gradient φ)) (hg : ContDiff ℝ 3 g) :
    LocallyLipschitz (weightedDiffusion φ g) := by
  have hmul : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 * p.2) := contDiff_fst.mul contDiff_snd
  have hi (i : Fin n) : LocallyLipschitz (fun x =>
      coordinateHessian g x i i - coordinateDerivative g i x * coordinateDerivative φ i x) := by
    have ha := (contDiff_coordinateHessian hg (m := 1) (by norm_num) i i).locallyLipschitz
    have hb := (contDiff_coordinateDerivative hg (m := 1) (by norm_num) i).locallyLipschitz
    have hp := hb.prodMk (locallyLipschitz_coordinateDerivative_of_gradient hG i)
    exact ha.sub (hmul.locallyLipschitz.comp hp)
  have hs (s : Finset (Fin n)) : LocallyLipschitz (fun x => ∑ i ∈ s,
      (coordinateHessian g x i i - coordinateDerivative g i x * coordinateDerivative φ i x)) := by
    classical
    induction s using Finset.induction_on with
    | empty =>
      have hz : ContDiff ℝ 1 (fun _ : Space n => (0 : ℝ)) := contDiff_const
      simpa using hz.locallyLipschitz
    | @insert a s ha ih => simpa only [Finset.sum_insert ha] using (hi a).add ih
  have he : weightedDiffusion φ g = fun x => ∑ i,
      (coordinateHessian g x i i - coordinateDerivative g i x * coordinateDerivative φ i x) :=
    funext (weightedDiffusion_eq_sum φ g)
  rw [he]
  exact hs Finset.univ

theorem coordinateDerivative_weightedDiffusion_at
    {φ g : Space n → ℝ} {x : Space n}
    (hφ : ∀ j, DifferentiableAt ℝ (coordinateDerivative φ j) x)
    (hg : ContDiff ℝ 3 g) (i : Fin n) :
    coordinateDerivative (weightedDiffusion φ g) i x =
      weightedDiffusion φ (coordinateDerivative g i) x -
        ∑ j, coordinateHessian φ x i j * coordinateDerivative g j x := by
  have heq : weightedDiffusion φ g = fun y => ∑ j,
      (coordinateHessian g y j j - coordinateDerivative g j y * coordinateDerivative φ j y) :=
    funext (weightedDiffusion_eq_sum φ g)
  have hdg (j : Fin n) : DifferentiableAt ℝ (coordinateDerivative g j) x :=
    (contDiff_coordinateDerivative hg (m := 1) (by norm_num) j).differentiable (by norm_num) x
  have hddg (j : Fin n) : DifferentiableAt ℝ (fun y => coordinateHessian g y j j) x :=
    (contDiff_coordinateHessian hg (m := 1) (by norm_num) j j).differentiable (by norm_num) x
  rw [heq, coordinateDerivative_sum
    (f := fun j y => coordinateHessian g y j j - coordinateDerivative g j y * coordinateDerivative φ j y)
    (fun j => (hddg j).sub ((hdg j).mul (hφ j)))]
  rw [weightedDiffusion_eq_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [coordinateDerivative_sub (f := fun y => coordinateHessian g y j j)
    (g := fun y => coordinateDerivative g j y * coordinateDerivative φ j y)
    (hddg j) ((hdg j).mul (hφ j)),
    coordinateDerivative_mul (hdg j) (hφ j), coordinateDerivative_diagonal_eq hg]
  have hsymm := (coordinateHessian_symmetric (hg.of_le (by norm_num)) x).apply i j
  change coordinateHessian (coordinateDerivative g i) x j j -
    (coordinateHessian g x i j * coordinateDerivative φ j x +
      coordinateDerivative g j x * coordinateHessian φ x i j) = _
  change coordinateHessian g x j i = coordinateHessian g x i j at hsymm
  rw [← hsymm]
  change coordinateHessian (coordinateDerivative g i) x j j -
    (coordinateDerivative (coordinateDerivative g i) j x * coordinateDerivative φ j x +
      coordinateDerivative g j x * coordinateHessian φ x i j) = _
  ring

/-- A C1,1 potential has the actual commutator almost everywhere. The
resulting derivative is also a genuine local weak derivative. -/
theorem weak_weightedDiffusion_commutator
    {φ g : Space n → ℝ} (hG : LocallyLipschitz (gradient φ)) (hg : ContDiff ℝ 3 g)
    (i : Fin n) :
    coordinateDerivative (weightedDiffusion φ g) i =ᵐ[volume]
      (fun x => weightedDiffusion φ (coordinateDerivative g i) x -
        ∑ j, coordinateHessian φ x i j * coordinateDerivative g j x) ∧
    HasLocalWeakCoordinateDerivative (weightedDiffusion φ g)
      (fun x => weightedDiffusion φ (coordinateDerivative g i) x -
        ∑ j, coordinateHessian φ x i j * coordinateDerivative g j x) i ∧
    (∀ S, IsCompact S → MemLp
      (fun x => weightedDiffusion φ (coordinateDerivative g i) x -
        ∑ j, coordinateHessian φ x i j * coordinateDerivative g j x) ∞ (volume.restrict S)) := by
  have he : coordinateDerivative (weightedDiffusion φ g) i =ᵐ[volume]
      (fun x => weightedDiffusion φ (coordinateDerivative g i) x -
        ∑ j, coordinateHessian φ x i j * coordinateDerivative g j x) := by
    have ha := ae_all_iff.mpr (fun j =>
      locallyLipschitz_ae_differentiableAt (μ := volume)
        (locallyLipschitz_coordinateDerivative_of_gradient hG j))
    filter_upwards [ha] with x hx
    exact coordinateDerivative_weightedDiffusion_at hx hg i
  have hloc := locallyLipschitz_weightedDiffusion hG hg
  refine ⟨he, (hasLocalWeakCoordinateDerivative_of_locallyLipschitz hloc i).congr_ae
    Filter.EventuallyEq.rfl he, ?_⟩
  intro S hS
  exact (memLp_congr_ae (ae_restrict_of_ae he)).mp
    (memLp_top_coordinateDerivative_of_locallyLipschitz hloc i hS)

end KLS
end
