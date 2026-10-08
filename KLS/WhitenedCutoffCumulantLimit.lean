import KLS.LogConcaveLaplaceJets
import KLS.FiniteMultilinearCoordinateLimit
import KLS.CumulantJetLimit
import KLS.WhitenedCutoffMoments

/-! Every genuine Laplace jet and cumulant tensor of the constructed
centered/whitened compact cutoffs converges in multilinear operator norm. -/
open MeasureTheory Filter Metric InnerProductSpace
open scoped ContDiff Topology BigOperators
noncomputable section
namespace KLS

theorem admissibleMeasure.tendsto_laplace_jet_whitenedBallCutoffMeasure
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0) (d : ℕ) :
    Tendsto (fun k => iteratedFDeriv ℝ d
      (fun z => tiltPartition (whitenedBallCutoffMeasure μ R k) (fun x => inner ℝ z x)) 0)
      atTop (𝓝 (iteratedFDeriv ℝ d (fun z => tiltPartition μ (fun x => inner ℝ z x)) 0)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  let : ∀ k, IsProbabilityMeasure (ballCutoffMeasure μ R k) :=
    fun k => isProbabilityMeasure_ballCutoffMeasure hR k
  let : ∀ k, IsProbabilityMeasure (whitenedBallCutoffMeasure μ R k) :=
    fun k => inferInstanceAs (IsProbabilityMeasure (whitenedMeasure (ballCutoffMeasure μ R k)))
  apply tendsto_multilinear_of_coordinate_evaluations
  intro a
  have he (k : ℕ) := measureLogConcave.iteratedFDeriv_laplace_coordinate_moment
    ((hμ.logConcave.ballCutoff_logConcave R k).whitenedMeasure) a
  simpa only [whitenedBallCutoffMeasure, he,
    hμ.logConcave.iteratedFDeriv_laplace_coordinate_moment a] using
    hμ.tendsto_coordinate_moment_whitenedBallCutoffMeasure hR a

theorem admissibleMeasure.tendsto_cumulantTensor_whitenedBallCutoffMeasure
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0) (m : ℕ) :
    Tendsto (fun k => cumulantTensor (whitenedBallCutoffMeasure μ R k) m)
      atTop (𝓝 (cumulantTensor μ m)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  let : ∀ k, IsProbabilityMeasure (ballCutoffMeasure μ R k) :=
    fun k => isProbabilityMeasure_ballCutoffMeasure hR k
  let : ∀ k, IsProbabilityMeasure (whitenedBallCutoffMeasure μ R k) :=
    fun k => inferInstanceAs (IsProbabilityMeasure (whitenedMeasure (ballCutoffMeasure μ R k)))
  apply tendsto_cumulantTensor_of_laplace_jets
  · intro k
    exact ((hμ.logConcave.ballCutoff_logConcave R k).whitenedMeasure).contDiffAt_laplace.of_le (by simp)
  · exact hμ.logConcave.contDiffAt_laplace.of_le (by simp)
  · intro k _
    exact hμ.tendsto_laplace_jet_whitenedBallCutoffMeasure hR k

end KLS
end
