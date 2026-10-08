import KLS.WeightedCompactSmoothing
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! Genuine compact smooth density in the weighted L2 space, obtained from
compact continuous density and the actual mollification sequence. -/

open MeasureTheory Set Filter Metric
open scoped ENNReal ContDiff Topology
noncomputable section
namespace KLS

def SmoothCompactL2 {n : ℕ} (V : Space n → ℝ) : Set (Lp ℝ 2 (potentialMeasure V)) :=
  {f | ∃ g : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
    ∃ hg : MemLp g 2 (potentialMeasure V), hg.toLp g = f}

lemma compactContinuous_mem_closure_smoothCompactL2 {n : ℕ} {V g : Space n → ℝ}
    (hV : Continuous V) (hg : Continuous g) (hc : HasCompactSupport g)
    (hgμ : MemLp g 2 (potentialMeasure V)) : hgμ.toLp g ∈ closure (SmoothCompactL2 V) := by
  have hgV : MemLp g 2 volume := hg.memLp_of_hasCompactSupport hc
  have hms (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (mollify k g) :=
    mollify_contDiff (hgV.locallyIntegrable (by norm_num)) k
  have hmc (k : ℕ) := hasCompactSupport_mollify hc k
  have hmμ (k : ℕ) : MemLp (mollify k g) 2 (potentialMeasure V) :=
    memLp_of_continuous_hasCompactSupport hV (hms k).continuous (hmc k)
  have ht : Tendsto (fun k => eLpNorm (mollify k g - g) 2 (potentialMeasure V)) atTop (𝓝 0) :=
    eLpNorm_potentialMeasure_sub_tendsto_zero_of_compact_support hV
      (isCompact_mollifierEnlargement hc) (tsupport_mollify_subset hc)
      (subset_mollifierEnlargement _) (fun k => memLp_mollify hgV k) hgV hmμ hgμ
      (eLpNorm_mollify_sub_tendsto_zero hgV)
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun k => mollify k g) hmμ g hgμ).mpr ht
  exact mem_closure_of_tendsto hLp (Eventually.of_forall (fun k =>
    ⟨mollify k g, hms k, hmc k, hmμ k, rfl⟩))

theorem dense_smoothCompactL2 {n : ℕ} {V : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure V)] (hV : Continuous V) :
    Dense (SmoothCompactL2 V) := by
  let S : Set (Lp ℝ 2 (potentialMeasure V)) :=
    {f | ∃ g : Space n → ℝ, Continuous g ∧ HasCompactSupport g ∧
      ∃ hg : MemLp g 2 (potentialMeasure V), hg.toLp g = f}
  have hd : Dense S := by
    intro f
    refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedEBall).2 fun ε hε => ?_
    obtain ⟨g, hc, hdist, hg, hgμ⟩ :=
      (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hε.ne'
    refine ⟨hgμ.toLp g, ⟨g, hg, hc, hgμ, rfl⟩, ?_⟩
    rwa [Metric.mem_closedEBall', ← Lp.toLp_coeFn f (Lp.memLp f), Lp.edist_toLp_toLp]
  have hs : S ⊆ closure (SmoothCompactL2 V) := by
    rintro f ⟨g, hg, hc, hgμ, rfl⟩
    exact compactContinuous_mem_closure_smoothCompactL2 hV hg hc hgμ
  intro f
  simpa only [closure_closure] using (closure_mono hs) (hd f)

theorem exists_smoothCompactL2_sequence {n : ℕ} {V : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure V)] (hV : Continuous V)
    (f : Lp ℝ 2 (potentialMeasure V)) :
    ∃ g : ℕ → Space n → ℝ, (∀ k, ContDiff ℝ (⊤ : ℕ∞) (g k) ∧ HasCompactSupport (g k)) ∧
      ∃ hg : ∀ k, MemLp (g k) 2 (potentialMeasure V),
        Tendsto (fun k => (hg k).toLp (g k)) atTop (𝓝 f) := by
  obtain ⟨u, hu, ht⟩ := mem_closure_iff_seq_limit.mp (dense_smoothCompactL2 hV f)
  choose g hgs hgc hgm he using hu
  refine ⟨g, fun k => ⟨hgs k, hgc k⟩, hgm, ?_⟩
  simpa only [he] using ht

end KLS
end
#print axioms KLS.dense_smoothCompactL2
#print axioms KLS.exists_smoothCompactL2_sequence
