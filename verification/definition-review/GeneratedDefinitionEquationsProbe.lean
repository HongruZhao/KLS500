import FinalKLSRange
import Lean.Util.CollectAxioms

open MeasureTheory Lean Elab Command

#check (KLS.potentialMeasure.eq_1 : ∀ {n : ℕ} (φ : KLS.Space n → ℝ),
  KLS.potentialMeasure φ = volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x))))

#check (KLS.tiltLogLaplace.eq_1 : ∀ {n : ℕ} (μ : Measure (KLS.Space n)) (z : KLS.Space n),
  KLS.tiltLogLaplace μ z = Real.log (KLS.tiltPartition μ (fun x => inner ℝ z x)))

#check (KLS.tiltThirdCumulant.eq_1 : ∀ {n : ℕ} (μ : Measure (KLS.Space n))
    (q f g h : KLS.Space n → ℝ),
  KLS.tiltThirdCumulant μ q f g h = KLS.tiltAverage μ q (fun x =>
    (f x - KLS.tiltAverage μ q f) * (g x - KLS.tiltAverage μ q g) *
    (h x - KLS.tiltAverage μ q h)))

example {n : ℕ} (φ : KLS.Space n → ℝ) :
  KLS.potentialMeasure φ = volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x))) := rfl

example {n : ℕ} (μ : Measure (KLS.Space n)) (z : KLS.Space n) :
  KLS.tiltLogLaplace μ z = Real.log (KLS.tiltPartition μ (fun x => inner ℝ z x)) := rfl

example {n : ℕ} (μ : Measure (KLS.Space n)) (q f g h : KLS.Space n → ℝ) :
  KLS.tiltThirdCumulant μ q f g h = KLS.tiltAverage μ q (fun x =>
    (f x - KLS.tiltAverage μ q f) * (g x - KLS.tiltAverage μ q g) *
    (h x - KLS.tiltAverage μ q h)) := rfl

run_cmd do
  let env ← getEnv
  let gates : Array (Name × Name × Bool) := #[
    (`KLS.potentialMeasure.eq_1, `KLS.WeightedEigenClassical, true),
    (`KLS.tiltLogLaplace.eq_1, `KLS.AdaptiveLogMGFSpatial, true),
    (`KLS.tiltThirdCumulant.eq_1, `KLS.CumulantBounds, true),
    (`KLS.potentialMeasure, `KLS.WeightedIntegrationByParts, false),
    (`KLS.tiltLogLaplace, `KLS.TiltFrechet, false),
    (`KLS.tiltThirdCumulant, `KLS.TiltCumulants, false)]
  let standard : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for (gate, origin, isTheorem) in gates do
    match env.find? gate with
    | some (.thmInfo _) => unless isTheorem do throwError "Wrong declaration kind: {gate}"
    | some (.defnInfo _) => if isTheorem then throwError "Wrong declaration kind: {gate}"
    | _ => throwError "Unexpected declaration: {gate}"
    match env.getModuleIdxFor? gate with
    | some idx => unless env.allImportedModuleNames[idx.toNat]! == origin do
        throwError "Wrong exact origin: {gate}"
    | none => throwError "Missing origin: {gate}"
    let axioms ← collectAxioms gate
    unless axioms.size == 3 && standard.all axioms.contains do
      throwError "Wrong axiom set: {gate}, {axioms}"
    logInfo m!"EQUATION_ORIGIN_OK {gate}|{origin}|{axioms}"
  logInfo "EQUATION_DEFINITION_GATES_PASSED 6"
