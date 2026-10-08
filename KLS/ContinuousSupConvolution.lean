import DifferentialGeometry.Analysis.Convex.SupConvolution
import Mathlib.Topology.UniformSpace.HeineCantor

open Set Filter Metric
open scoped Topology NNReal
noncomputable section
namespace KLS
open DifferentialGeometry.Analysis.Convex

lemma le_supConvolutionOn_of_bddAbove {X : Type*} [PseudoMetricSpace X]
    {u : X → ℝ} {s : Set X} (hu : BddAbove (u '' s))
    {ε : ℝ} (hε : 0 < ε) {x : X} (hx : x ∈ s) :
    u x ≤ supConvolutionOn s u ε x := by
  obtain ⟨M, hM⟩ := hu
  have hb : BddAbove ((fun y => u y - dist x y ^ 2 / (2 * ε)) '' s) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (sub_le_self _ (by positivity)).trans (hM (mem_image_of_mem _ hy))
  simpa only [dist_self, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero,
    supConvolutionOn] using le_csSup hb (mem_image_of_mem _ hx)

lemma supConvolution_maximizer_dist_sq_le {X : Type*} [PseudoMetricSpace X]
    {u : X → ℝ} {s : Set X} {M : ℝ} (hM : ∀ z ∈ s, |u z| ≤ M)
    {ε : ℝ} (hε : 0 < ε) {x y : X} (hx : x ∈ s) (hy : y ∈ s)
    (hmax : supConvolutionOn s u ε x = u y - dist x y ^ 2 / (2 * ε)) :
    dist x y ^ 2 ≤ 4 * ε * M := by
  have hb : BddAbove (u '' s) := ⟨M, by
    rintro _ ⟨z, hz, rfl⟩
    exact (le_abs_self _).trans (hM z hz)⟩
  have hlo := le_supConvolutionOn_of_bddAbove hb hε hx
  rw [hmax] at hlo
  have hpen : dist x y ^ 2 / (2 * ε) ≤ 2 * M := by
    have hx' := (abs_le.mp (hM x hx)).1
    have hy' := (abs_le.mp (hM y hy)).2
    linarith
  have hmul := (div_le_iff₀ (show 0 < 2 * ε by positivity)).mp hpen
  nlinarith

lemma supConvolution_maximizer_dist_lt {X : Type*} [PseudoMetricSpace X]
    {u : X → ℝ} {s : Set X} {M δ ε : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ z ∈ s, |u z| ≤ M) (hδ : 0 < δ) (hε : 0 < ε)
    (hsmall : ε < δ ^ 2 / (4 * (M + 1)))
    {x y : X} (hx : x ∈ s) (hy : y ∈ s)
    (hmax : supConvolutionOn s u ε x = u y - dist x y ^ 2 / (2 * ε)) :
    dist x y < δ := by
  have hd := supConvolution_maximizer_dist_sq_le hbound hε hx hy hmax
  have hs := (lt_div_iff₀ (show 0 < 4 * (M + 1) by positivity)).mp hsmall
  nlinarith [dist_nonneg (x := x) (y := y)]

lemma tendstoUniformlyOn_supConvolutionOn_of_continuousOn
    {X : Type*} [PseudoMetricSpace X] {u : X → ℝ} {s : Set X}
    (hs : IsCompact s) (hu : ContinuousOn u s) :
    TendstoUniformlyOn (fun ε => supConvolutionOn s u ε) u (𝓝[>] (0 : ℝ)) s := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuousOn hu
  have hM0 : 0 ≤ M := by
    obtain ⟨x, hx⟩ := hne
    exact (norm_nonneg (u x)).trans (hM x hx)
  have hbound : ∀ x ∈ s, |u x| ≤ M := by simpa only [Real.norm_eq_abs] using hM
  have huc := hs.uniformContinuousOn_of_continuous hu
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  obtain ⟨δ, hδ, hclose⟩ := huc η hη
  have ha : 0 < δ ^ 2 / (4 * (M + 1)) := by positivity
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < δ ^ 2 / (4 * (M + 1)) from
      (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds)] with ε hε he x hx
  change 0 < ε at hε
  obtain ⟨y, hy, hmax⟩ := exists_supConvolutionOn_eq_of_isCompact hs hne
    hu.upperSemicontinuousOn ε x
  have hd := supConvolution_maximizer_dist_lt hM0 hbound hδ hε he hx hy hmax
  have hv := hclose x hx y hy hd
  have hlo := le_supConvolutionOn_of_bddAbove (hs.bddAbove_image hu) hε hx
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hlo)]
  rw [hmax]
  have hcost : 0 ≤ dist x y ^ 2 / (2 * ε) := by positivity
  have hval : u y - u x < η := by
    rw [Real.dist_eq, abs_sub_comm] at hv
    exact (le_abs_self _).trans_lt hv
  linarith

end KLS
end
