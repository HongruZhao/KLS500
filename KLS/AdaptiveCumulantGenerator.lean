import KLS.AdaptiveCumulantDerivatives

/-! Mixed spatial-state differentiation of the actual cumulant generator. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.StandardLocalization
variable {n m : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem coordinateLogMGF_word (hμ : IsCompact μ.support) (w : Space n)
    (vs : List (Fin (n+n*n) → ℝ)) (z : Fin (n+n*n) → ℝ) :
    directionalWordDerivative (coordinateLogMGF μ w) vs z =
      directionalWordDerivative (coordinateLogPartition μ) vs (z+linearStateCLM w) -
        directionalWordDerivative (coordinateLogPartition μ) vs z := by
  have he : coordinateLogMGF μ w = fun y =>
      coordinateLogPartition μ (y+linearStateCLM w) - coordinateLogPartition μ y :=
    funext (fun y => coordinateLogMGF_eq_partition_difference hμ y w)
  rw [he]
  have hf := contDiff_coordinateLogPartition hμ
  have hshift : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => coordinateLogPartition μ (y+linearStateCLM w)) :=
    hf.comp (contDiff_id.add contDiff_const)
  rw [directionalWordDerivative_sub hshift hf,
    directionalWordDerivative_comp_add_right hf]

/-- The coefficients are frozen at the actual state z; x is only the partition argument. -/
def frozenPartitionGenerator (μ : Measure (Space n))
    (z x : Fin (n+n*n) → ℝ) : ℝ :=
  directionalWordDerivative (coordinateLogPartition μ) [coordinateDrift μ z] x +
    1/2 * ∑ k : Fin n, directionalWordDerivative (coordinateLogPartition μ)
      [coordinateDiffusion μ k z, coordinateDiffusion μ k z] x

theorem contDiff_frozenPartitionGenerator (hμ : IsCompact μ.support)
    (z : Fin (n+n*n) → ℝ) : ContDiff ℝ (⊤ : ℕ∞) (frozenPartitionGenerator μ z) :=
  (contDiff_directionalWordDerivative (contDiff_coordinateLogPartition hμ) _).add
    (contDiff_const.mul (ContDiff.sum fun k _ =>
      contDiff_directionalWordDerivative (contDiff_coordinateLogPartition hμ) _))

/-- Exact finite-dimensional identity differentiated to obtain higher cumulant drifts. -/
theorem frozenPartitionGenerator_difference (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (z : Fin (n+n*n) → ℝ) (w : Space n) :
    frozenPartitionGenerator μ z (z+linearStateCLM w) - frozenPartitionGenerator μ z z =
      logMGFDrift μ w z := by
  have hg := coordinateLogMGF_generator hμ hfull w z
  have he1 : coordinateLogMGFGradient μ w z (coordinateDrift μ z) =
      directionalWordDerivative (coordinateLogMGF μ w) [coordinateDrift μ z] z := rfl
  have he2 (k : Fin n) : coordinateLogMGFHessian μ w z (coordinateDiffusion μ k z)
      (coordinateDiffusion μ k z) = directionalWordDerivative (coordinateLogMGF μ w)
        [coordinateDiffusion μ k z, coordinateDiffusion μ k z] z :=
    fderiv_fderiv_apply_eq_word (contDiff_coordinateLogMGF hμ w) z _ _
  rw [he1] at hg
  simp_rw [he2, coordinateLogMGF_word hμ w] at hg
  unfold frozenPartitionGenerator
  rw [Finset.sum_sub_distrib] at hg
  linarith

def cumulantGenerator (μ : Measure (Space n)) (m : ℕ) (h : Fin m → Space n)
    (z : Fin (n+n*n) → ℝ) : ℝ :=
  coordinateCumulantGradient μ m h z (coordinateDrift μ z) +
    1/2 * ∑ k : Fin n, coordinateCumulantHessian μ m h z
      (coordinateDiffusion μ k z) (coordinateDiffusion μ k z)

theorem frozenPartitionGenerator_word (hμ : IsCompact μ.support) (hm : m ≠ 0)
    (h : Fin m → Space n) (z : Fin (n+n*n) → ℝ) :
    directionalWordDerivative (frozenPartitionGenerator μ z)
      ((List.ofFn h).map linearStateCLM) z = cumulantGenerator μ m h z := by
  let vs := (List.ofFn h).map linearStateCLM
  have hf := contDiff_coordinateLogPartition hμ
  have hD := contDiff_directionalWordDerivative hf [coordinateDrift μ z]
  have hS (k : Fin n) := contDiff_directionalWordDerivative hf
    [coordinateDiffusion μ k z, coordinateDiffusion μ k z]
  change directionalWordDerivative (fun x =>
    directionalWordDerivative (coordinateLogPartition μ) [coordinateDrift μ z] x +
    1/2 * ∑ k, directionalWordDerivative (coordinateLogPartition μ)
      [coordinateDiffusion μ k z, coordinateDiffusion μ k z] x) vs z = _
  rw [directionalWordDerivative_add hD (contDiff_const.mul (ContDiff.sum fun k _ => hS k)),
    directionalWordDerivative_const_mul (ContDiff.sum fun k _ => hS k),
    directionalWordDerivative_sum _ (fun k _ => hS k)]
  simp_rw [directionalWordDerivative_append]
  unfold cumulantGenerator
  rw [coordinateCumulantGradient_apply hμ hm]
  simp_rw [coordinateCumulantHessian_apply hμ hm]
  congr 1
  · exact congrFun (directionalWordDerivative_perm hf (List.perm_append_comm)) z
  · congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact congrFun (directionalWordDerivative_perm hf (List.perm_append_comm)) z

/-- The actual generator equals the genuine spatial derivative of the proved log-MGF drift.
All differentiation is deterministic C∞ calculus; no stochastic interchange is assumed. -/
theorem cumulantGenerator_eq_spatial_derivative (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hm : m ≠ 0) (h : Fin m → Space n)
    (z : Fin (n+n*n) → ℝ) :
    cumulantGenerator μ m h z =
      directionalWordDerivative (fun w => logMGFDrift μ w z) (List.ofFn h) 0 := by
  have he : (fun w => logMGFDrift μ w z) = fun w =>
      frozenPartitionGenerator μ z (z+linearStateCLM w) - frozenPartitionGenerator μ z z :=
    funext (fun w => (frozenPartitionGenerator_difference hμ hfull z w).symm)
  rw [he]
  have hf := contDiff_frozenPartitionGenerator hμ z
  have hs : ContDiff ℝ (⊤ : ℕ∞)
      (fun w : Space n => frozenPartitionGenerator μ z (z+linearStateCLM w)) :=
    hf.comp (contDiff_const.add linearStateCLM.contDiff)
  rw [directionalWordDerivative_sub hs (contDiff_const (c := frozenPartitionGenerator μ z z))]
  have hne : List.ofFn h ≠ [] := by
    intro hh
    apply hm
    simpa only [List.length_ofFn, List.length_nil] using congrArg List.length hh
  rw [directionalWordDerivative_const_of_ne_nil _ _ hne]
  simp only [Pi.zero_apply, sub_zero]
  rw [directionalWordDerivative_comp_affine hf]
  simp only [map_zero, add_zero]
  exact (frozenPartitionGenerator_word hμ hm h z).symm

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.cumulantGenerator_eq_spatial_derivative
