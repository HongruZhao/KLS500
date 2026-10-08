import KLS.WeightedSuccessorIteration
import KLS.WeightedSuccessorBochner

/-! Actual smooth diffusion-domain representatives at every level of the
literal normalized tensor recursion. The sequence is constructed from the
proved Poisson regularity theorem, not postulated as an admissible orbit. -/

open MeasureTheory InnerProductSpace Matrix Filter
open scoped ContDiff RealInnerProductSpace ENNReal

noncomputable section
namespace KLS
variable {n : ℕ}

theorem continuous_representative_unique {f g : Space n → ℝ}
    (hf : Continuous f) (hg : Continuous g) (h : f =ᵐ[volume] g) : f = g :=
  Measure.eq_of_ae_eq h hf hg

variable {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

/-- Starting with an actual smooth graph representative in the diffusion
domain, every literal normalized iterate has such a representative. -/
theorem exists_weightedIteration_smooth_representatives
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι) (f : ι → Space n → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hv : ∀ i, f i =ᵐ[volume] (weightedH1Value φ (U i) : Space n → ℝ))
    (hL : ∀ i, MemLp (weightedDiffusion φ (f i)) 2 (potentialMeasure φ)) :
    ∃ F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ,
      F 0 = f ∧
      (∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i)) ∧
      (∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i) : Space n → ℝ)) ∧
      ∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ) := by
  let hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  have hall (k : ℕ) : ∃ fk : WeightedIterationIndex n ι k → Space n → ℝ,
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fk i)) ∧
      (∀ i, fk i =ᵐ[volume] (weightedH1Value φ
        (weightedSuccessorIterate hφ2 hκ hlower U k i) : Space n → ℝ)) ∧
      ∀ i, MemLp (weightedDiffusion φ (fk i)) 2 (potentialMeasure φ) := by
    induction k with
    | zero => exact ⟨f, hf, hv, hL⟩
    | succ k ih =>
      obtain ⟨fk, hfk, hvk, _⟩ := ih
      obtain ⟨gnext, hg⟩ := weightedNormalizedSuccessor_exists_smooth_representative
        hφ hκ hlower (weightedSuccessorIterate hφ2 hκ hlower U k) fk hfk hvk
      exact ⟨gnext, fun i => (hg i).1, fun i => (hg i).2.2.2.1, fun i => (hg i).2.2.2.2.2⟩
  choose F hF hV hLF using hall
  have hzero : F 0 = f := by
    funext i
    exact continuous_representative_unique (hF 0 i).continuous (hf i).continuous
      ((hV 0 i).trans (hv i).symm)
  exact ⟨F, hzero, hF, hV, hLF⟩

/-- Any continuous representatives of the actual iterates obey the genuine
pointwise normalized Poisson recursion, by uniqueness of representatives. -/
theorem weightedIteration_smooth_successor_equation
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
    (F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ)
    (hF : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i))
    (hV : ∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i) : Space n → ℝ))
    (k : ℕ) (ji : Fin n × WeightedIterationIndex n ι k) (x : Space n) :
    weightedDiffusion φ (F (k + 1) ji) x =
      -(weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k) *
          (coordinateDerivative (F k ji.2) ji.1 x -
            ∫ y, coordinateDerivative (F k ji.2) ji.1 y ∂potentialMeasure φ)) := by
  obtain ⟨gnext, hg⟩ := weightedNormalizedSuccessor_exists_smooth_representative
    hφ hκ hlower (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k)
      (F k) (hF k) (hV k)
  have he : F (k + 1) ji = gnext ji := continuous_representative_unique
    (hF (k + 1) ji).continuous (hg ji).1.continuous
    ((hV (k + 1) ji).trans (hg ji).2.2.2.1.symm)
  rw [he]
  exact (hg ji).2.2.2.2.1 x

end KLS
end

#print axioms KLS.exists_weightedIteration_smooth_representatives
#print axioms KLS.weightedIteration_smooth_successor_equation
