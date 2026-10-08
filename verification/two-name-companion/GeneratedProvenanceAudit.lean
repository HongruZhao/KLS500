import FinalKLSRange
import Lean.Util.CollectAxioms

open Lean Elab Command MeasureTheory ProbabilityTheory
open scoped BigOperators

#check (KLS.matrixFrobeniusSq.eq_1 :
  ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ),
    KLS.matrixFrobeniusSq M = ∑ i : Fin n, ∑ j : Fin n, (M i j) ^ 2)

#check (KLS.CenteredExponential.instIsProbabilityMeasureRealExpMeasureOfNat_kLS_1 :
  IsProbabilityMeasure (expMeasure 1))

run_cmd do
  let env ← getEnv
  let gates : Array (Name × Name) := #[
    (`KLS.matrixFrobeniusSq.eq_1, `KLS.SteinMatrixContraction),
    (`KLS.CenteredExponential.instIsProbabilityMeasureRealExpMeasureOfNat_kLS_1,
      `KLS.ExponentialPoincare)]
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
    unless axs.size == 3 && axs.all (fun ax => allowed.contains ax) do
      throwError "Unexpected axiom closure: {gate}: {axs}"
    logInfo m!"GENERATED_HELPER_OK {gate}|{origin}|theorem|{axs}"
  logInfo m!"GENERATED_HELPERS_PASSED {gates.size}"

#print axioms KLS.matrixFrobeniusSq.eq_1
#print axioms KLS.CenteredExponential.instIsProbabilityMeasureRealExpMeasureOfNat_kLS_1
