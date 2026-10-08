import KLS.ContinuousSupConvolution
import DifferentialGeometry.Analysis.Viscosity.SupConvolution

open Set Filter Metric
open scoped Topology NNReal
noncomputable section
namespace KLS
open DifferentialGeometry.Analysis.Convex

/-- Continuous data suffice for constant-coefficient upper-test transfer.
The bounded oscillation estimate forces the actual maximizer into the interior. -/
theorem upper_test_supConvolutionOn_of_continuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {s : Set E} (hs : IsCompact s) (hu : ContinuousOn u s)
    {M δ ε : ℝ} (hM : 0 ≤ M) (hbound : ∀ z ∈ s, |u z| ≤ M)
    (hδ : 0 < δ) (hε : 0 < ε) (hsmall : ε < δ ^ 2 / (4 * (M + 1)))
    {x : E} (hx : closedBall x δ ⊆ interior s)
    {H : ℝ → (E →L[ℝ] ℝ) → (E →L[ℝ] E →L[ℝ] ℝ) → ℝ}
    (hH : ∀ p B, Monotone (fun r => H r p B))
    (hsub : ∀ y ∈ interior s, ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      IsLocalMax (fun z => u z - ψ z) y →
      H (u y) (fderiv ℝ ψ y) (fderiv ℝ (fderiv ℝ ψ) y) ≤ 0)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hm : IsLocalMax (fun z => supConvolutionOn s u ε z - φ z) x) :
    H (supConvolutionOn s u ε x) (fderiv ℝ φ x) (fderiv ℝ (fderiv ℝ φ) x) ≤ 0 := by
  have hxs : x ∈ s := interior_subset (hx (mem_closedBall_self hδ.le))
  obtain ⟨y, hy, hmax⟩ := exists_supConvolutionOn_eq_of_isCompact hs ⟨x, hxs⟩
    hu.upperSemicontinuousOn ε x
  have hyi : y ∈ interior s := by
    apply hx
    rw [mem_closedBall, dist_comm]
    exact (supConvolution_maximizer_dist_lt hM hbound hδ hε hsmall hxs hy hmax).le
  have hb := hs.bddAbove_image hu
  have htest := isLocalMax_sub_translate_of_supConvolutionOn hb hε hyi hmax hm
  have htranslate (z : E) : x + (z - y) = z + (x - y) := by abel
  simp_rw [htranslate] at htest
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun z => φ (z + (x - y))) :=
    hφ.comp (contDiff_id.add contDiff_const)
  have hle := hsub y hyi _ hsmooth htest
  have hxy : y + (x - y) = x := by abel
  have hD : fderiv ℝ (fun z => φ (z + (x - y))) y = fderiv ℝ φ x := by
    rw [DifferentialGeometry.Analysis.fderiv_translate φ (x - y) y
      (hφ.differentiable (by simp) _), hxy]
  have hDD : fderiv ℝ (fderiv ℝ (fun z => φ (z + (x - y)))) y =
      fderiv ℝ (fderiv ℝ φ) x := by
    have hφ2 : ContDiff ℝ 2 φ := hφ.of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
    rw [DifferentialGeometry.Analysis.fderiv_fderiv_translate φ hφ2 (x - y) y, hxy]
  rw [hD, hDD] at hle
  apply le_trans (hH _ _ ?_) hle
  rw [hmax]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (by positivity))

end KLS
end
