import KLS.WeightedNormalizedSuccessor

/-! Actual repeated normalized successors, with increasing tensor rank.
The energy monotonicity and telescoping identity are consequences of this
specific recursion, not hypotheses on an abstract sequence. -/

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace ENNReal

noncomputable section
namespace KLS

def WeightedIterationIndex (n : ℕ) (ι : Type*) : ℕ → Type _
  | 0 => ι
  | k + 1 => Fin n × WeightedIterationIndex n ι k

instance weightedIterationIndexFintype (n : ℕ) (ι : Type*) [Fintype ι] (k : ℕ) :
    Fintype (WeightedIterationIndex n ι k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype ι)
  | succ k ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Fin n × WeightedIterationIndex n ι k))

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

/-- The genuine BKL iteration, starting from any actual finite energy family. -/
def weightedSuccessorIterate {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι) :
    (k : ℕ) → WeightedH1Family φ (WeightedIterationIndex n ι k)
  | 0 => U
  | k + 1 => weightedNormalizedSuccessor hφ hκ hlower (weightedSuccessorIterate U k)

@[simp] theorem weightedSuccessorIterate_zero {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι) :
    weightedSuccessorIterate hφ hκ hlower U 0 = U := rfl

@[simp] theorem weightedSuccessorIterate_succ {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (k : ℕ) :
    weightedSuccessorIterate hφ hκ hlower U (k + 1) =
      weightedNormalizedSuccessor hφ hκ hlower (weightedSuccessorIterate hφ hκ hlower U k) := rfl

def weightedIterationEnergy {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι) (k : ℕ) : ℝ :=
  ‖weightedFamilyGradient φ (WeightedIterationIndex n ι k) (weightedSuccessorIterate hφ hκ hlower U k)‖ ^ 2

def weightedIterationMeanLoss {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι) (k : ℕ) : ℝ :=
  ∑ ji : Fin n × WeightedIterationIndex n ι k,
    (∫ x, weightedFamilyGradient φ (WeightedIterationIndex n ι k)
      (weightedSuccessorIterate hφ hκ hlower U k) ji x ∂potentialMeasure φ) ^ 2

theorem weightedIterationEnergy_nonneg {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (k : ℕ) : 0 ≤ weightedIterationEnergy hφ hκ hlower U k := sq_nonneg _

theorem weightedIterationMeanLoss_nonneg {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (k : ℕ) : 0 ≤ weightedIterationMeanLoss hφ hκ hlower U k :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- BKL (35) for the actual recursively constructed tensor families. -/
theorem weightedIterationEnergy_sub_succ {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (k : ℕ) :
    weightedIterationEnergy hφ hκ hlower U k - weightedIterationEnergy hφ hκ hlower U (k + 1) =
      weightedIterationMeanLoss hφ hκ hlower U k :=
  weightedNormalizedSuccessor_energy_defect hφ hκ hlower (weightedSuccessorIterate hφ hκ hlower U k)

theorem weightedIterationEnergy_antitone {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) : Antitone (weightedIterationEnergy hφ hκ hlower U) := by
  apply antitone_nat_of_succ_le
  intro k
  have h := weightedIterationEnergy_sub_succ hφ hκ hlower U k
  have hp := weightedIterationMeanLoss_nonneg hφ hκ hlower U k
  linarith

/-- BKL (36) with arbitrary initial energy, proved for the literal recursion. -/
theorem weightedIterationEnergy_telescope {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (N : ℕ) :
    ‖weightedFamilyGradient φ ι U‖ ^ 2 = weightedIterationEnergy hφ hκ hlower U N +
      ∑ k ∈ Finset.range N, weightedIterationMeanLoss hφ hκ hlower U k := by
  induction N with
  | zero =>
    simp only [weightedIterationEnergy, weightedSuccessorIterate_zero, Finset.range_zero,
      Finset.sum_empty, add_zero]
    rfl
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h := weightedIterationEnergy_sub_succ hφ hκ hlower U N
    linarith

/-- Every scale in the actual iteration is controlled by the same attained eigenvalue. -/
theorem exists_optimal_weightedIterationScale_lower_bound (hn : 0 < n) :
    ∃ lam : ℝ, 0 < lam ∧
      poincareConstant (potentialMeasure φ) = ENNReal.ofReal lam⁻¹ ∧
      ∀ (ι : Type*) [Fintype ι] (U : WeightedH1Family φ ι) (k : ℕ),
        weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι k)
          (weightedSuccessorIterate hφ hκ hlower U k) ≠ 0 →
            lam ≤ (weightedSuccessorScale hφ hκ hlower (weightedSuccessorIterate hφ hκ hlower U k)) ^ 2 := by
  obtain ⟨lam, hlam, hCP, hb⟩ := exists_optimal_weightedSuccessorScale_lower_bound hφ hκ hlower hn
  exact ⟨lam, hlam, hCP, fun ι _ U k => hb _ (weightedSuccessorIterate hφ hκ hlower U k)⟩

end KLS
end

#print axioms KLS.weightedIterationEnergy_sub_succ
#print axioms KLS.weightedIterationEnergy_antitone
#print axioms KLS.weightedIterationEnergy_telescope
#print axioms KLS.exists_optimal_weightedIterationScale_lower_bound
