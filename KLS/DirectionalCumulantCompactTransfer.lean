import KLS.WhitenedCutoffCumulantLimit
import KLS.SuspensionCumulantTaylorBound
import KLS.DensityToClass

/-! The genuine directional Hilbert-Schmidt square passes to the actual
compact-cutoff limit. A bound proved for compact laws suffices on the full
original class, with exactly the same constant and cumulant order. -/
open MeasureTheory Filter Metric
open scoped ContDiff Topology BigOperators
noncomputable section
namespace KLS

theorem admissibleMeasure.tendsto_directionalCumulantSquare_whitenedBallCutoffMeasure
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0) (d : ℕ) (u : Space n) :
    Tendsto (fun k => directionalCumulantSquare (whitenedBallCutoffMeasure μ R k) d u)
      atTop (𝓝 (directionalCumulantSquare μ d u)) := by
  have hT := hμ.tendsto_cumulantTensor_whitenedBallCutoffMeasure hR (d+1)
  have ha (a : Fin d → Fin n) :
      Tendsto (fun k => cumulantTensor (whitenedBallCutoffMeasure μ R k) (d+1)
        (Fin.snoc (fun j => EuclideanSpace.basisFun (Fin n) ℝ (a j)) u)) atTop
        (𝓝 (cumulantTensor μ (d+1)
          (Fin.snoc (fun j => EuclideanSpace.basisFun (Fin n) ℝ (a j)) u))) := by
    have hc : Continuous (fun M : ContinuousMultilinearMap ℝ
        (fun _ : Fin (d+1) => Space n) ℝ =>
          M (Fin.snoc (fun j => EuclideanSpace.basisFun (Fin n) ℝ (a j)) u)) := by fun_prop
    exact hc.continuousAt.tendsto.comp hT
  exact tendsto_finsetSum Finset.univ (fun a _ => (ha a).pow 2)

theorem admissibleMeasure.directionalCumulantSquare_le_of_compact
    {n d : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (b : ℝ)
    (hcompact : ∀ ν : Measure (Space n), admissibleMeasure ν → IsCompact ν.support →
      ∀ u : Space n, directionalCumulantSquare ν d u ≤ b * ‖u‖ ^ 2)
    (u : Space n) : directionalCumulantSquare μ d u ≤ b * ‖u‖ ^ 2 := by
  obtain ⟨R, _, hR, he⟩ := hμ.exists_whitened_compact_cutoffs
  apply le_of_tendsto (hμ.tendsto_directionalCumulantSquare_whitenedBallCutoffMeasure hR d u)
  filter_upwards [he] with k hk
  exact hcompact (whitenedBallCutoffMeasure μ R k) hk.1 hk.2 u

theorem universalDirectionalCumulantBound_of_compact {d : ℕ} {b : ℝ}
    (hcompact : ∀ n : ℕ, ∀ μ : Measure (Space n), IsKLSMeasure μ →
      IsCompact μ.support → ∀ u : Space n, directionalCumulantSquare μ d u ≤ b * ‖u‖ ^ 2) :
    UniversalDirectionalCumulantBound d b := by
  intro n μ hμ u
  exact hμ.admissibleMeasure.directionalCumulantSquare_le_of_compact b
    (fun ν hν hνc => hcompact n ν hν.isKLSMeasure hνc) u

end KLS
end
