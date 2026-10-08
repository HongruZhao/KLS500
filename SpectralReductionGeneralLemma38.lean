import SpectralReductionGeneralDoubling
import SpectralReductionExactLemma38
import KLS.WeightedIterationTaylorEnergy

/-! Exact central-binomial coefficients in actual BKL Lemma 3.8. The named
symmetrization property is discharged by genuine finite-group estimates. -/

open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction
set_option backward.isDefEq.respectTransparency false

def generalTaylorMainCoefficient (M : ℝ) (d : ℕ) : ℝ :=
  2 * ((2 * d).choose d : ℝ) ^ 2 * M ^ d

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
  (F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ)
  (W : (k : ℕ) → WeightedH1Family φ (Fin n × WeightedIterationIndex n ι k))
  (hF : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i))
  (hV : ∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
    (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i) : Space n → ℝ))
  (hL : ∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ))

/-- A coefficient for the norm of the actual averaged gradient error. The
argument m of σ is the number q+1 of symmetrized derivative slots. -/
def WeightedIterationGeneralSymmetrizationCoefficientBound (lam M : ℝ) (σ : ℕ → ℝ) : Prop :=
  ∀ r q : ℕ,
    (∀ k, r + 1 ≤ k → k < r + q →
      (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k)) ^ 2 ≤ M * lam) →
    ‖weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + q))
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + q)) -
      weightedIterationSymmetrizedGradient (hφ.of_le (by simp)) hκ hlower U r q‖ ^ 2 ≤
        σ (q + 1) / lam * ∑ i : Fin q, weightedIterationDefect hφ hκ hlower U W (r + i)

include hF hV hL

theorem weightedIteration_taylor_doubling_generalScale_exact
    {lam M : ℝ} {σ β : ℕ → ℝ}
    (hβ : WeightedCoordinateTaylorCoefficientBound φ β) (hβ0 : ∀ d, 0 ≤ β d)
    (hsym : WeightedIterationGeneralSymmetrizationCoefficientBound hφ hκ hlower U W lam M σ)
    (r d s : ℕ) (hd : 1 ≤ d) (hs : s + 1 = d)
    (hscale : ∀ k, r ≤ k → k < r + (s + d) →
      (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k)) ^ 2 ≤ M * lam) :
    weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U d (r + (s + d)) ≤
      generalTaylorMainCoefficient M d * lam ^ d *
        weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U (2 * d) (r + s) +
      exactTaylorErrorCoefficient σ d * β d / lam *
        ∑ i : Fin (s + d), weightedIterationDefect hφ hκ hlower U W (r + i) := by
  have hg := hsym r (s + d) (fun k hk hkj => hscale k (by omega) hkj)
  rw [show s + d + 1 = 2 * d by omega] at hg
  have he := weightedIteration_taylor_doubling_generalScale hφ hκ hlower U F W hF hV hL
    hβ hβ0 r d s hd hs hscale hg
  convert he using 1 <;>
    simp only [generalTaylorMainCoefficient, exactTaylorErrorCoefficient,
      weightedIterationTaylorEnergy, mul_pow] <;> ring

theorem weightedIteration_taylor_generalScale_exact
    {lam M : ℝ} {σ β : ℕ → ℝ}
    (hβ : WeightedCoordinateTaylorCoefficientBound φ β) (hβ0 : ∀ d, 0 ≤ β d)
    (hsym : WeightedIterationGeneralSymmetrizationCoefficientBound hφ hκ hlower U W lam M σ)
    (d k : ℕ) (hd : 1 ≤ d) (hk : 2 * d ≤ k + 1)
    (hscale : ∀ j < k, (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U j)) ^ 2 ≤ M * lam) :
    weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U d k ≤
      generalTaylorMainCoefficient M d * lam ^ d *
        weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U (2 * d) (k - d) +
      exactTaylorErrorCoefficient σ d * β d / lam *
        ∑ i : Fin (2 * d - 1), weightedIterationDefect hφ hκ hlower U W (k - (2 * d - 1) + i) := by
  have hq : d - 1 + d = 2 * d - 1 := by omega
  have hcur : k - (2 * d - 1) + (d - 1 + d) = k := by omega
  have hprev : k - (2 * d - 1) + (d - 1) = k - d := by omega
  have he := weightedIteration_taylor_doubling_generalScale_exact hφ hκ hlower U F W hF hV hL
    hβ hβ0 hsym (k - (2 * d - 1)) d (d - 1) hd (by omega)
      (fun j _ hj => hscale j (by omega))
  rw [hcur, hprev] at he
  have hsum : (∑ i : Fin (d - 1 + d),
      weightedIterationDefect hφ hκ hlower U W (k - (2 * d - 1) + i)) =
      ∑ i : Fin (2 * d - 1), weightedIterationDefect hφ hκ hlower U W (k - (2 * d - 1) + i) := by
    let f : ℕ → ℝ := fun j => weightedIterationDefect hφ hκ hlower U W (k - (2 * d - 1) + j)
    change (∑ i : Fin (d - 1 + d), f i) = ∑ i : Fin (2 * d - 1), f i
    rw [Fin.sum_univ_eq_sum_range f (d - 1 + d), Fin.sum_univ_eq_sum_range f (2 * d - 1), hq]
  rw [hsum] at he
  exact he

/-- Direct stopping-index form: the per-step bounds already proved before N
supply the scale hypotheses, on the identical actual iteration. -/
theorem weightedIteration_taylor_generalScale_exact_before_stop
    {lam M : ℝ} {σ β : ℕ → ℝ}
    (hβ : WeightedCoordinateTaylorCoefficientBound φ β) (hβ0 : ∀ d, 0 ≤ β d)
    (hsym : WeightedIterationGeneralSymmetrizationCoefficientBound hφ hκ hlower U W lam M σ)
    (N : ℕ)
    (hscale : ∀ j, j + 1 < N → (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U j)) ^ 2 ≤ M * lam)
    (d k : ℕ) (hd : 1 ≤ d) (hk : 2 * d ≤ k + 1) (hkN : k < N) :
    weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U d k ≤
      generalTaylorMainCoefficient M d * lam ^ d *
        weightedIterationTaylorEnergy (hφ.of_le (by simp)) hκ hlower U (2 * d) (k - d) +
      exactTaylorErrorCoefficient σ d * β d / lam *
        ∑ i : Fin (2 * d - 1), weightedIterationDefect hφ hκ hlower U W (k - (2 * d - 1) + i) :=
  weightedIteration_taylor_generalScale_exact hφ hκ hlower U F W hF hV hL hβ hβ0 hsym d k hd hk
    (fun j hj => hscale j (by omega))


end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.weightedIteration_taylor_doubling_generalScale_exact
#print axioms KLS.ConstantReduction.weightedIteration_taylor_generalScale_exact
#print axioms KLS.ConstantReduction.weightedIteration_taylor_generalScale_exact_before_stop
