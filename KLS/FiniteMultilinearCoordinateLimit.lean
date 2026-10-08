import KLS.LocalTiltNumeratorMoments

/-! Finite coordinate convergence is actual operator-norm convergence for
multilinear maps on Euclidean space; no weak topology is substituted. -/
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
noncomputable section
namespace KLS
variable {n d : ℕ}

lemma space_eq_sum_single (x : Space n) :
    x = ∑ i : Fin n, x i • EuclideanSpace.single i 1 := by
  apply PiLp.ext
  intro j
  change x j = (EuclideanSpace.proj j) (∑ i : Fin n, x i • EuclideanSpace.single i 1)
  rw [map_sum]
  simp

theorem multilinear_eq_coordinate_sum
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin d => Space n) ℝ)
    (v : Fin d → Space n) :
    M v = ∑ a : Fin d → Fin n, (∏ j, v j (a j)) *
      M (fun j => EuclideanSpace.single (a j) 1) := by
  have hv : v = fun j => ∑ i : Fin n, v j i • EuclideanSpace.single i 1 :=
    funext fun j => space_eq_sum_single (v j)
  conv_lhs => rw [hv]
  rw [M.map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [M.map_smul_univ]
  rfl

theorem norm_multilinear_le_coordinate_sum
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin d => Space n) ℝ) :
    ‖M‖ ≤ ∑ a : Fin d → Fin n, ‖M (fun j => EuclideanSpace.single (a j) 1)‖ := by
  apply M.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  rw [multilinear_eq_coordinate_sum M v]
  calc
    _ ≤ ∑ a : Fin d → Fin n,
        ‖(∏ j, v j (a j)) * M (fun j => EuclideanSpace.single (a j) 1)‖ := norm_sum_le _ _
    _ = ∑ a : Fin d → Fin n, (∏ j, ‖v j (a j)‖) *
        ‖M (fun j => EuclideanSpace.single (a j) 1)‖ := by simp only [norm_mul, norm_prod]
    _ ≤ ∑ a : Fin d → Fin n, (∏ j, ‖v j‖) *
        ‖M (fun j => EuclideanSpace.single (a j) 1)‖ := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun j _ => PiLp.norm_apply_le (v j) (a j))
    _ = (∑ a : Fin d → Fin n, ‖M (fun j => EuclideanSpace.single (a j) 1)‖) * ∏ j, ‖v j‖ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem tendsto_multilinear_of_coordinate_evaluations {ι : Type*} {l : Filter ι}
    {M : ι → ContinuousMultilinearMap ℝ (fun _ : Fin d => Space n) ℝ}
    {L : ContinuousMultilinearMap ℝ (fun _ : Fin d => Space n) ℝ}
    (h : ∀ a : Fin d → Fin n,
      Tendsto (fun i => M i (fun j => EuclideanSpace.single (a j) 1)) l
        (𝓝 (L (fun j => EuclideanSpace.single (a j) 1)))) :
    Tendsto M l (𝓝 L) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs : Tendsto (fun i => ∑ a : Fin d → Fin n,
      ‖M i (fun j => EuclideanSpace.single (a j) 1) -
        L (fun j => EuclideanSpace.single (a j) 1)‖) l (𝓝 0) := by
    simpa only [sub_self, norm_zero, Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun a _ => ((h a).sub
        (tendsto_const_nhds : Tendsto (fun _ : ι => L (fun j => EuclideanSpace.single (a j) 1)) l
          (𝓝 (L (fun j => EuclideanSpace.single (a j) 1))))).norm)
  apply squeeze_zero (fun _ => norm_nonneg _) _ hs
  intro i
  simpa only [sub_apply] using norm_multilinear_le_coordinate_sum (M i - L)

end KLS
end
