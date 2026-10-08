import FinalKLSRange
import Lean.Util.CollectAxioms

open Lean Elab Command
open MeasureTheory ProbabilityTheory

example : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
  KLS.CenteredExponential.instIsProbabilityMeasureRealExpMeasureOfNat_kLS_1

set_option pp.all true in
run_cmd do
  let env ← getEnv
  let name := `KLS.CenteredExponential.instIsProbabilityMeasureRealExpMeasureOfNat_kLS_1
  let some ci := env.find? name | throwError "missing exact generated instance"
  let .thmInfo thm := ci | throwError "generated instance is not a theorem"
  let some idx := env.getModuleIdxFor? name | throwError "missing generated instance origin"
  let origin := env.allImportedModuleNames[idx.toNat]!
  unless origin == `KLS.ExponentialPoincare do
    throwError "unexpected fresh generated instance origin: {origin}"
  unless ci.levelParams.isEmpty do
    throwError "unexpected universe parameters"
  let axioms ← collectAxioms name
  unless axioms.size == 3 && axioms.contains `propext &&
      axioms.contains `Classical.choice && axioms.contains `Quot.sound do
    throwError "unexpected axiom set: {axioms}"
  logInfo m!"NAME {name}"
  logInfo m!"KIND theorem"
  logInfo m!"ORIGIN {origin}"
  logInfo m!"AXIOMS {axioms}"
  logInfo m!"LEVELS {repr ci.levelParams}"
  logInfo m!"RAW_TYPE {repr ci.type}"
  logInfo m!"RAW_PROOF {repr thm.value}"
  logInfo m!"TYPE {ci.type}"
  logInfo m!"PROOF {thm.value}"
  logInfo "END_DUMP"
