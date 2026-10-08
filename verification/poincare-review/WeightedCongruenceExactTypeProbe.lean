import FinalKLSRange
open MeasureTheory Matrix
open scoped BigOperators ContDiff
universe u
set_option format.width 160
set_option pp.proofs true
#check (KLS.weightedIterationEnergy.congr_simp :
  ∀ {n : ℕ} {φ : KLS.Space n → ℝ} {κ κ' : ℝ} (eκ : κ = κ')
    [IsProbabilityMeasure (KLS.potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ (x : KLS.Space n) (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (KLS.coordinateHessian φ x *ᵥ a))
    {ι : Type u} [Fintype ι] (U U' : KLS.WeightedH1Family φ ι), U = U' →
    ∀ k k' : ℕ, k = k' →
      KLS.weightedIterationEnergy hφ hκ hlower U k =
        KLS.weightedIterationEnergy hφ (eκ ▸ hκ) (eκ ▸ hlower) U' k')
#print axioms KLS.weightedIterationEnergy.congr_simp
#check (KLS.matrixFrobeniusSq.eq_1 : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ),
  KLS.matrixFrobeniusSq M = ∑ i : Fin n, ∑ j : Fin n, (M i j)^2)
#print axioms KLS.matrixFrobeniusSq.eq_1
#check (KLS.coordinateDerivative_sq : ∀ {n : ℕ} {f : KLS.Space n → ℝ},
  Differentiable ℝ f → ∀ (i : Fin n) (x : KLS.Space n),
    KLS.coordinateDerivative (fun y => f y ^ 2) i x = 2*f x*KLS.coordinateDerivative f i x)
#print axioms KLS.coordinateDerivative_sq
