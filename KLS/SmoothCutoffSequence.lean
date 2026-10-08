import KLS.WeightedCaccioppoli

/-! # Actual smooth compact cutoffs with uniformly vanishing gradient bounds -/

open MeasureTheory InnerProductSpace Filter
open scoped Topology ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

lemma gradient_comp_const_smul {f : Space n → ℝ} (hf : Differentiable ℝ f)
    (c : ℝ) (x : Space n) :
    gradient (fun y => f (c • y)) x = c • gradient f (c • x) := by
  have hi : HasFDerivAt (fun y : Space n => c • y)
      (c • ContinuousLinearMap.id ℝ (Space n)) x := (hasFDerivAt_id x).const_smul c
  have he := (hf (c • x)).hasFDerivAt.comp x hi
  have hd : fderiv ℝ (fun y => f (c • y)) x = c • fderiv ℝ f (c • x) := by
    change fderiv ℝ (f ∘ fun y => c • y) x = _
    rw [he.fderiv]
    ext v
    simp
  unfold gradient
  rw [hd]
  simp

def unitCutoff (n : ℕ) : ContDiffBump (0 : Space n) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def cutoffScale (k : ℕ) : ℝ := ((k : ℝ) + 1)⁻¹

lemma cutoffScale_pos (k : ℕ) : 0 < cutoffScale k := by
  unfold cutoffScale
  positivity

lemma cutoffScale_tendsto_zero : Tendsto cutoffScale atTop (𝓝 0) := by
  apply tendsto_inv_atTop_zero.comp
  exact tendsto_atTop_mono (fun k : ℕ => le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 by norm_num))
    tendsto_natCast_atTop_atTop

def smoothCutoff (n : ℕ) (k : ℕ) (x : Space n) : ℝ :=
  unitCutoff n (cutoffScale k • x)

lemma smoothCutoff_contDiff (k : ℕ) : ContDiff ℝ 1 (smoothCutoff n k) :=
  (unitCutoff n).contDiff.comp (contDiff_id.const_smul (cutoffScale k))

lemma smoothCutoff_hasCompactSupport (k : ℕ) : HasCompactSupport (smoothCutoff n k) :=
  (unitCutoff n).hasCompactSupport.comp_smul (cutoffScale_pos k).ne'

lemma smoothCutoff_tendsto_one (x : Space n) :
    Tendsto (fun k => smoothCutoff n k x) atTop (𝓝 1) := by
  have hb : unitCutoff n (0 : Space n) = 1 :=
    (unitCutoff n).one_of_mem_closedBall (by simp [unitCutoff])
  have ht : Tendsto (fun k => cutoffScale k • x) atTop (𝓝 (0 : Space n)) := by
    simpa using cutoffScale_tendsto_zero.smul_const x
  simpa only [smoothCutoff, hb, Function.comp_def] using
    (unitCutoff n).continuous.continuousAt.tendsto.comp ht

/-- The constant comes from the derivative of a single actual compact smooth bump. -/
theorem smoothCutoff_gradient_bound : ∃ K : ℝ, 0 ≤ K ∧
    ∀ k x, ‖gradient (smoothCutoff n k) x‖ ≤ cutoffScale k * K := by
  have hb : ContDiff ℝ 1 (unitCutoff n) := (unitCutoff n).contDiff
  obtain ⟨K, hK⟩ := (hasCompactSupport_gradient (unitCutoff n).hasCompactSupport).exists_bound_of_continuous
    (continuous_gradient_of_contDiff hb)
  refine ⟨K, (norm_nonneg _).trans (hK 0), ?_⟩
  intro k x
  change ‖gradient (fun y => unitCutoff n (cutoffScale k • y)) x‖ ≤ _
  rw [gradient_comp_const_smul (hb.differentiable (by norm_num)), norm_smul,
    Real.norm_eq_abs, abs_of_pos (cutoffScale_pos k)]
  exact mul_le_mul_of_nonneg_left (hK _) (cutoffScale_pos k).le

end KLS
end

#print axioms KLS.gradient_comp_const_smul
#print axioms KLS.smoothCutoff_tendsto_one
#print axioms KLS.smoothCutoff_gradient_bound
