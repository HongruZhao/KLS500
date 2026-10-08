import KLS.LocalizationSmooth

/-! Bounds on actual centered third moments under compact-support tilts. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
noncomputable section
namespace KLS.FiniteFeatureTilt

/-- Three bounded observables have a bounded actual third cumulant. -/
theorem norm_tiltThirdCumulant_le_of_bounds {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    {q f g h : Space n → ℝ} (hq : Continuous q)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂μ.tilted q, ‖f x‖ ≤ A)
    (hg : ∀ᵐ x ∂μ.tilted q, ‖g x‖ ≤ B)
    (hh : ∀ᵐ x ∂μ.tilted q, ‖h x‖ ≤ C) :
    ‖tiltThirdCumulant μ q f g h‖ ≤ 8 * A * B * C := by
  letI := tilted_isProbability_of_compact_support hμ hq
  have hfa : ‖tiltAverage μ q f‖ ≤ A := by
    simpa only [tiltAverage, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hf
  have hga : ‖tiltAverage μ q g‖ ≤ B := by
    simpa only [tiltAverage, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hg
  have hha : ‖tiltAverage μ q h‖ ≤ C := by
    simpa only [tiltAverage, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hh
  have hb : ∀ᵐ x ∂μ.tilted q,
      ‖(f x - tiltAverage μ q f) * (g x - tiltAverage μ q g) *
          (h x - tiltAverage μ q h)‖ ≤ 8 * A * B * C := by
    filter_upwards [hf, hg, hh] with x hx hy hz
    have hx' : ‖f x - tiltAverage μ q f‖ ≤ 2 * A :=
      (norm_sub_le _ _).trans (by linarith)
    have hy' : ‖g x - tiltAverage μ q g‖ ≤ 2 * B :=
      (norm_sub_le _ _).trans (by linarith)
    have hz' : ‖h x - tiltAverage μ q h‖ ≤ 2 * C :=
      (norm_sub_le _ _).trans (by linarith)
    rw [norm_mul, norm_mul]
    calc _ ≤ (2 * A) * (2 * B) * (2 * C) := by gcongr
      _ = _ := by ring
  simpa only [tiltThirdCumulant, tiltAverage, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hb

end KLS.FiniteFeatureTilt
end
#print axioms KLS.FiniteFeatureTilt.norm_tiltThirdCumulant_le_of_bounds
