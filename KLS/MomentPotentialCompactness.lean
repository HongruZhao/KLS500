import KLS.Definitions
import Mathlib.Analysis.Convex.FunctionTopology
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Compactness of normalized convex potentials with a common Lipschitz bound

This module extracts actual subsequences converging locally uniformly on all of
Euclidean space. Convexity, normalization, and the Lipschitz bound are retained.
No variational optimizer or transport equation is assumed.
-/

open Filter Set
open scoped Topology NNReal

noncomputable section
namespace KLS

/-- Convex potentials with a specified common Lipschitz bound and value zero at
the origin, as a subset of the continuous maps with the compact-open topology. -/
def normalizedConvexLipschitzPotentials (n : ℕ) (L : ℝ≥0) : Set C(Space n, ℝ) :=
  {f | LipschitzWith L f ∧ f 0 = 0 ∧ ConvexOn ℝ Set.univ f}

theorem isClosed_pointwise_normalizedConvexLipschitzPotentials (n : ℕ) (L : ℝ≥0) :
    IsClosed {f : Space n → ℝ | LipschitzWith L f ∧ f 0 = 0 ∧ ConvexOn ℝ Set.univ f} := by
  exact (isClosed_setOfPred_lipschitzWith L).inter
    ((isClosed_eq (continuous_apply 0) continuous_const).inter isClosed_setOfPred_convexOn)

theorem normalizedConvexLipschitzPotentials_pointwise_bound
    {n : ℕ} {L : ℝ≥0} {f : Space n → ℝ} (hLip : LipschitzWith L f) (hzero : f 0 = 0)
    (x : Space n) : |f x| ≤ L * ‖x‖ := by
  have h := hLip.dist_le_mul x 0
  simpa only [hzero, Real.dist_eq, sub_zero, dist_zero_right, Real.norm_eq_abs] using h

/-- Tychonoff compactness in the pointwise topology, with explicit bounds at
every point, before upgrading to compact convergence. -/
theorem isCompact_pointwise_normalizedConvexLipschitzPotentials (n : ℕ) (L : ℝ≥0) :
    IsCompact {f : Space n → ℝ | LipschitzWith L f ∧ f 0 = 0 ∧ ConvexOn ℝ Set.univ f} := by
  apply IsCompact.of_isClosed_subset
    (isCompact_univ_pi (fun x : Space n => isCompact_Icc (a := -(L * ‖x‖)) (b := L * ‖x‖)))
    (isClosed_pointwise_normalizedConvexLipschitzPotentials n L)
  intro f hf x _
  exact abs_le.mp (normalizedConvexLipschitzPotentials_pointwise_bound hf.1 hf.2.1 x)

/-- The normalized family is compact for uniform convergence on compact sets.
This invokes the full compact-open Arzelà--Ascoli theorem, so the conclusion
simultaneously covers every compact subset of the noncompact source space. -/
theorem isCompact_normalizedConvexLipschitzPotentials (n : ℕ) (L : ℝ≥0) :
    IsCompact (normalizedConvexLipschitzPotentials n L) := by
  apply ArzelaAscoli.isCompact_of_equicontinuous
  · have heq : ContinuousMap.toFun '' normalizedConvexLipschitzPotentials n L =
        {f : Space n → ℝ | LipschitzWith L f ∧ f 0 = 0 ∧ ConvexOn ℝ Set.univ f} := by
      ext f
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact hg
      · intro hf
        exact ⟨⟨f, hf.1.continuous⟩, hf, rfl⟩
    rw [heq]
    exact isCompact_pointwise_normalizedConvexLipschitzPotentials n L
  · exact (LipschitzWith.uniformEquicontinuous
      (fun f : normalizedConvexLipschitzPotentials n L => (f.1 : Space n → ℝ)) L
      (fun f => f.2.1)).equicontinuous

/-- Every sequence in the family admits one strictly increasing subsequence
converging locally uniformly to a convex potential with the same normalization
and Lipschitz bound. The same subsequence converges uniformly on every compact
set; no subsequence or convergence certificate is an input hypothesis. -/
theorem exists_subseq_normalizedConvexLipschitzPotentials
    {n : ℕ} (L : ℝ≥0) (f : ℕ → Space n → ℝ)
    (hLip : ∀ k, LipschitzWith L (f k)) (hzero : ∀ k, f k 0 = 0)
    (hconvex : ∀ k, ConvexOn ℝ Set.univ (f k)) :
    ∃ (g : Space n → ℝ) (s : ℕ → ℕ),
      StrictMono s ∧ LipschitzWith L g ∧ g 0 = 0 ∧ ConvexOn ℝ Set.univ g ∧
      TendstoLocallyUniformly (fun k => f (s k)) g atTop ∧
      ∀ K : Set (Space n), IsCompact K → TendstoUniformlyOn (fun k => f (s k)) g atTop K := by
  let F : ℕ → C(Space n, ℝ) := fun k => ⟨f k, (hLip k).continuous⟩
  have hF (k : ℕ) : F k ∈ normalizedConvexLipschitzPotentials n L :=
    ⟨hLip k, hzero k, hconvex k⟩
  obtain ⟨g, hg, s, hs, hlim⟩ := (isCompact_normalizedConvexLipschitzPotentials n L).tendsto_subseq hF
  refine ⟨g, s, hs, hg.1, hg.2.1, hg.2.2, ?_, ?_⟩
  · exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hlim
  · exact ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hlim

end KLS
end

#print axioms KLS.isCompact_normalizedConvexLipschitzPotentials
#print axioms KLS.exists_subseq_normalizedConvexLipschitzPotentials
