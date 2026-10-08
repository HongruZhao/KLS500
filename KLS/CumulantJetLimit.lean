import KLS.FiniteJetCompositionLimit

/-! The actual cumulant tensors converge whenever the genuine finite jets of
the Laplace transforms converge. Probability normalization fixes the common
logarithm base point at one; no alternative definition of cumulants is used. -/

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace KLS

theorem tendsto_cumulantTensor_of_laplace_jets {n m : ℕ} {ι : Type*}
    {l : Filter ι} {μ : ι → Measure (Space n)} {ν : Measure (Space n)}
    [∀ a, IsProbabilityMeasure (μ a)] [IsProbabilityMeasure ν]
    (hμ : ∀ a, ContDiffAt ℝ m (fun z => tiltPartition (μ a) (fun x => inner ℝ z x)) 0)
    (hν : ContDiffAt ℝ m (fun z => tiltPartition ν (fun x => inner ℝ z x)) 0)
    (hjets : ∀ k ≤ m,
      Tendsto (fun a => iteratedFDeriv ℝ k
        (fun z => tiltPartition (μ a) (fun x => inner ℝ z x)) 0) l
        (𝓝 (iteratedFDeriv ℝ k (fun z => tiltPartition ν (fun x => inner ℝ z x)) 0))) :
    Tendsto (fun a => cumulantTensor (μ a) m) l (𝓝 (cumulantTensor ν m)) := by
  have hvalue (a : ι) : tiltPartition (μ a) (fun x => inner ℝ (0 : Space n) x) = 1 := by
    simp [tiltPartition]
  have hvalueν : tiltPartition ν (fun x => inner ℝ (0 : Space n) x) = 1 := by
    simp [tiltPartition]
  exact tendsto_iteratedFDeriv_comp_common_value hμ hν
    (Real.contDiffAt_log.mpr one_ne_zero) hvalue hvalueν hjets

end KLS
end
