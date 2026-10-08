import FinalKLSRange
import Lean.Util.CollectAxioms

open Lean Elab Command MeasureTheory ProbabilityTheory
open Matrix
open scoped BigOperators ContDiff
universe u
set_option pp.proofs true
set_option format.width 160

#check (KLS.matrixFrobeniusSq.eq_1 :
  ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ),
    KLS.matrixFrobeniusSq M = ∑ i : Fin n, ∑ j : Fin n, (M i j) ^ 2)

#check (KLS.CenteredExponential.instIsProbabilityMeasureRealExpMeasureOfNat_kLS_1 :
  IsProbabilityMeasure (expMeasure 1))


#check (KLS.potentialMeasure.eq_1 : ∀ {n : ℕ} (φ : KLS.Space n → ℝ),
  KLS.potentialMeasure φ = volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x))))

#check (KLS.tiltLogLaplace.eq_1 : ∀ {n : ℕ} (μ : Measure (KLS.Space n)) (z : KLS.Space n),
  KLS.tiltLogLaplace μ z = Real.log (KLS.tiltPartition μ (fun x => inner ℝ z x)))

#check (KLS.tiltThirdCumulant.eq_1 : ∀ {n : ℕ} (μ : Measure (KLS.Space n))
    (q f g h : KLS.Space n → ℝ),
  KLS.tiltThirdCumulant μ q f g h = KLS.tiltAverage μ q (fun x =>
    (f x - KLS.tiltAverage μ q f) * (g x - KLS.tiltAverage μ q g) *
    (h x - KLS.tiltAverage μ q h)))

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
#check (KLS.coordinateDerivative_sq : ∀ {n : ℕ} {f : KLS.Space n → ℝ},
  Differentiable ℝ f → ∀ (i : Fin n) (x : KLS.Space n),
    KLS.coordinateDerivative (fun y => f y ^ 2) i x = 2*f x*KLS.coordinateDerivative f i x)
run_cmd do
  let env ← getEnv
  let gates : Array (Name × Name) := #[
    (`KLS.matrixFrobeniusSq.eq_1, `KLS.SteinMatrixContraction),
    (`KLS.CenteredExponential.instIsProbabilityMeasureRealExpMeasureOfNat_kLS_1, `KLS.ExponentialPoincare),
    (`KLS.coordinateDerivative_sq, `KLS.WeightedDiffusionSquare),
    (`KLS.potentialMeasure.eq_1, `KLS.WeightedEigenClassical),
    (`KLS.tiltLogLaplace.eq_1, `KLS.AdaptiveLogMGFSpatial),
    (`KLS.tiltThirdCumulant.eq_1, `KLS.CumulantBounds),
    (`KLS.weightedIterationEnergy.congr_simp, `KLS.WeightedIterationBochner)]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for (gate, origin) in gates do
    match env.find? gate with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Unexpected declaration kind: {gate}"
    match env.getModuleIdxFor? gate with
    | some idx => unless env.allImportedModuleNames[idx.toNat]! == origin do
        throwError "Unexpected defining module: {gate}"
    | none => throwError "Missing defining module: {gate}"
    let axs ← collectAxioms gate
    unless axs.size == 3 && allowed.all axs.contains do
      throwError "Unexpected axiom closure: {gate}: {axs}"
    logInfo m!"SELECTED_ORIGIN_OK {gate}|{origin}|theorem|{axs}"
  logInfo m!"SELECTED_ORIGIN_GATES_PASSED {gates.size}"

#print axioms KLS.matrixFrobeniusSq.eq_1
#print axioms KLS.CenteredExponential.instIsProbabilityMeasureRealExpMeasureOfNat_kLS_1
#print axioms KLS.coordinateDerivative_sq
#print axioms KLS.potentialMeasure.eq_1
#print axioms KLS.tiltLogLaplace.eq_1
#print axioms KLS.tiltThirdCumulant.eq_1
#print axioms KLS.weightedIterationEnergy.congr_simp
