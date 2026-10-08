import KLS.BoundedWeightedMollification

/-! Smooth approximation for compact locally Lipschitz tests under every finite absolutely continuous measure. -/
open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal
noncomputable section
namespace KLS
variable {n : ℕ}

theorem compact_locallyLipschitz_absolutelyContinuous_smoothing
    {μ : Measure (Space n)} [IsFiniteMeasure μ] (hμ : μ ≪ volume)
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (hc : HasCompactSupport f) :
    (∀ k, ContDiff ℝ 3 (mollify k f) ∧ HasCompactSupport (mollify k f) ∧
      MemLp (mollify k f) 2 μ ∧
      ∀ i : Fin n, MemLp (coordinateDerivative (mollify k f) i) 2 μ) ∧
    Tendsto (fun k => eLpNorm (mollify k f - f) 2 μ) atTop (𝓝 0) ∧
    ∀ i : Fin n, Tendsto (fun k => eLpNorm
      (coordinateDerivative (mollify k f) i - coordinateDerivative f i) 2 μ)
      atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hf.continuous
  have hfb : ∀ᵐ x ∂volume, ‖f x‖ ≤ |B| :=
    Eventually.of_forall fun x => (hB x).trans (le_abs_self B)
  have hfv : MemLp f 2 volume := hf.continuous.memLp_of_hasCompactSupport hc
  have hfli := hfv.locallyIntegrable (by norm_num)
  have hfs := bounded_mollify_weighted_L2_convergence hμ hfli (abs_nonneg B) hfb
  obtain ⟨C, hC, hdb⟩ := compact_locallyLipschitz_coordinateDerivative_bound hf hc
  have hd (i : Fin n) :
      (∀ k, MemLp (coordinateDerivative (mollify k f) i) 2 μ) ∧
      Tendsto (fun k => eLpNorm
        (coordinateDerivative (mollify k f) i - coordinateDerivative f i) 2 μ)
        atTop (𝓝 0) := by
    have hdv := memLp_volume_compact_coordinateDerivative hf hc i
    let g : Lp ℝ 2 volume := hdv.toLp (coordinateDerivative f i)
    have hg : (g : Space n → ℝ) =ᵐ[volume] coordinateDerivative f i := hdv.coeFn_toLp
    have hgb : ∀ᵐ x ∂volume, ‖g x‖ ≤ C := hg.mono fun x hx => by rw [hx]; exact hdb i x
    have hw := locallyLipschitz_hasWeakCoordinateDerivative hf i hg
    have hs := bounded_mollify_weighted_L2_convergence hμ
      ((Lp.memLp g).locallyIntegrable (by norm_num)) hC hgb
    have hgμ : (g : Space n → ℝ) =ᵐ[μ] coordinateDerivative f i := hμ.ae_eq hg
    refine ⟨fun k => ?_, ?_⟩
    · rw [hw.mollify_eq hfv k]
      exact hs.1 k
    · have he (k : ℕ) : eLpNorm
          (coordinateDerivative (mollify k f) i - coordinateDerivative f i) 2 μ =
          eLpNorm (mollify k (g : Space n → ℝ) - (g : Space n → ℝ)) 2 μ := by
        rw [hw.mollify_eq hfv k]
        exact eLpNorm_congr_ae (EventuallyEq.rfl.sub hgμ.symm)
      simpa only [he] using hs.2.2
  exact ⟨fun k => ⟨(mollify_contDiff hfli k).of_le (by simp),
    hasCompactSupport_mollify hc k, hfs.1 k, fun i => (hd i).1 k⟩,
    hfs.2.2, fun i => (hd i).2⟩

end KLS
end
