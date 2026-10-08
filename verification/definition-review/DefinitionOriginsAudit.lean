import DefinitionIdentityAudit
open Lean Elab Command
set_option pp.proofs false
set_option pp.fullNames true

run_cmd do
  let env ← getEnv
  let gates : Array (Name × Name × String) := #[
    (`OAI.LeanBlast.KLS.Space, `OAI.Analysis.KLS.Model, "def"),
    (`OAI.LeanBlast.KLS.densityMeasure, `OAI.Analysis.KLS.Model, "def"),
    (`OAI.LeanBlast.KLS.IsLogConcaveDensity, `OAI.Analysis.KLS.Model, "inductive"),
    (`OAI.LeanBlast.KLS.IsIsotropic, `OAI.Analysis.KLS.Model, "inductive"),
    (`OAI.LeanBlast.KLS.expectation, `OAI.Analysis.KLS.Model, "def"),
    (`OAI.LeanBlast.KLS.variance, `OAI.Analysis.KLS.Model, "def"),
    (`OAI.LeanBlast.KLS.dirichletEnergy, `OAI.Analysis.KLS.Model, "def"),
    (`OAI.LeanBlast.KLS.IsTestFunction, `OAI.Analysis.KLS.Model, "def"),
    (`OAI.LeanBlast.KLS.PoincareBound, `OAI.Analysis.KLS.Model, "def"),
    (`OAI.LeanBlast.KLS.KLSStatement, `OAI.Analysis.KLS.Model, "def"),
    (`OAI.LeanBlast.KLS.FullStatement, `OAI.Analysis.KLS.Model, "def"),
    (`KLS.Space, `KLS.Definitions, "def"),
    (`KLS.IsIsotropic, `KLS.Definitions, "def"),
    (`KLS.HasLogConcaveDensity, `KLS.Definitions, "def"),
    (`KLS.IsKLSMeasure, `KLS.Definitions, "inductive"),
    (`KLS.admissibleMeasure, `KLS.Definitions, "inductive"),
    (`KLS.measureLogConcave, `KLS.Definitions, "def"),
    (`KLS.energy, `KLS.Definitions, "def"),
    (`KLS.variance, `KLS.Definitions, "def"),
    (`KLS.poincareConstants, `KLS.Definitions, "def"),
    (`KLS.cheegerConstant, `KLS.Definitions, "def"),
    (`KLS.KLSConjecture, `KLS.Definitions, "def"),
    (`KLS.admissibleMeasure_iff_isKLSMeasure, `KLS.DensityToClass, "theorem"),
    (`KLS.OpenAIBridge.admissible, `OpenAIKLSBridge, "theorem"),
    (`KLS.OpenAIBridge.poincareBound_of_mem, `OpenAIKLSBridge, "theorem"),
    (`OAI.LeanBlast.KLS.poincareBound500, `OpenAIKLS500, "theorem"),
    (`OAI.LeanBlast.KLS.klsStatement500, `OpenAIKLS500, "theorem"),
    (`KLS.admissibleMeasure.poincare_mem_coupledRankYoung, `CoupledRankYoungFullVerification, "theorem"),
    (`KLS.admissibleMeasure.cheeger_lower_entropy197_500, `Entropy197500FullVerification, "theorem"),
    (`KLS.exactOpenAIKLSStatement_entropy197_500, `Entropy197500FullVerification, "theorem"),
    (`KLS.dimensionFree500_and_cheeger197, `Entropy197500FullVerification, "theorem")]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for (gate, origin, wantedKind) in gates do
    match env.find? gate with
    | some (.thmInfo _) => unless wantedKind == "theorem" do throwError "Wrong kind: {gate}"
    | some (.defnInfo _) => unless wantedKind == "def" do throwError "Wrong kind: {gate}"
    | some (.inductInfo _) => unless wantedKind == "inductive" do throwError "Wrong kind: {gate}"
    | _ => throwError "Unexpected declaration: {gate}"
    match env.getModuleIdxFor? gate with
    | some idx => unless env.allImportedModuleNames[idx.toNat]! == origin do
        throwError "Wrong defining module: {gate}"
    | none => throwError "Missing defining module: {gate}"
    let axs ← collectAxioms gate
    unless (axs.filter (fun ax => !allowed.contains ax)).isEmpty do
      throwError "Nonstandard axiom in {gate}: {axs}"
    logInfo m!"DEFINITION_ORIGIN_OK {gate}|{origin}|{wantedKind}|{axs}"
  logInfo m!"DEFINITION_ORIGINS_PASSED {gates.size}"

#print OAI.LeanBlast.KLS.Space

#print OAI.LeanBlast.KLS.densityMeasure

#print OAI.LeanBlast.KLS.IsLogConcaveDensity

#print OAI.LeanBlast.KLS.IsIsotropic

#print OAI.LeanBlast.KLS.expectation

#print OAI.LeanBlast.KLS.variance

#print OAI.LeanBlast.KLS.dirichletEnergy

#print OAI.LeanBlast.KLS.IsTestFunction

#print OAI.LeanBlast.KLS.PoincareBound

#print OAI.LeanBlast.KLS.KLSStatement

#print OAI.LeanBlast.KLS.FullStatement

#print KLS.Space

#print KLS.IsIsotropic

#print KLS.HasLogConcaveDensity

#print KLS.IsKLSMeasure

#print KLS.admissibleMeasure

#print KLS.measureLogConcave

#print KLS.energy

#print KLS.variance

#print KLS.poincareConstants

#print KLS.cheegerConstant

#print KLS.KLSConjecture

#print KLS.admissibleMeasure_iff_isKLSMeasure

#print KLS.OpenAIBridge.admissible

#print KLS.OpenAIBridge.poincareBound_of_mem

#print OAI.LeanBlast.KLS.poincareBound500

#print OAI.LeanBlast.KLS.klsStatement500

#print KLS.admissibleMeasure.poincare_mem_coupledRankYoung

#print KLS.admissibleMeasure.cheeger_lower_entropy197_500

#print KLS.exactOpenAIKLSStatement_entropy197_500

#print KLS.dimensionFree500_and_cheeger197
