import Mathlib.Data.Real.Basic
import ViaLeanMathlib

open Lean Meta Elab Tactic ViaLean ViaLean.Mathlib

elab "mathlib_retrieval_guard" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let snap ← snapshot goal
    let candidates ← libraryPremiseProvider.retrieve snap 128
    unless !candidates.isEmpty do
      throwError "mathlib environment produced no premise candidates"
    for candidate in candidates do
      unless (← getEnv).contains candidate.name do
        throwError "retrieval lost or fabricated theorem name {candidate.name}"
    let some candidate := candidates.find? (fun item => item.name == ``Real.zero_lt_one)
      | throwError "mathlib retrieval did not preserve the expected Real.zero_lt_one name; candidates={repr (candidates.map (·.name))}"
    let cfg : ProposeConfig := {
      timeoutSec := 10
      directProbeSec := 0
      candidateProbeSec := 0
      structural := false
      cuts := false
      library := false
      nativeTransforms := false
      nativeCases := false
    }
    let proposals ← libraryCutProposals snap cfg #[candidate]
    let some proposal := proposals.find? (fun item =>
        match item.payload with
        | .libraryApply name => name == ``Real.zero_lt_one
        | _ => false)
      | throwError "retrieved Real.zero_lt_one was not compiled into a named proposal"
    let some proof ← runManualProposal goal cfg proposal
      | throwError "retrieved Real.zero_lt_one proposal could not be replayed"
    goal.assign proof
    replaceMainGoal []

elab "mathlib_model_syntax_guard" : tactic => do
  let env ← getEnv
  for code in #["by norm_num", "by omega", "by linarith", "by ring_nf", "by aesop"] do
    if (parseSafeModelTactic env code).isOk then
      throwError "mathlib syntax unexpectedly entered the dependency-free allowlist: {code}"
    match parseSafeModelTacticWithKinds env code mathlibModelSyntaxKinds with
    | .ok _ => pure ()
    | .error error => throwError "reviewed mathlib model tactic was rejected: {code}: {error}"
  if (parseSafeModelTacticWithKinds env
      "by run_tac IO.println \"unsafe\"" mathlibModelSyntaxKinds).isOk then
    throwError "mathlib model capabilities bypassed the run_tac prohibition"
  let goal ← getMainGoal
  goal.assign (mkConst ``True.intro)
  replaceMainGoal []

example : True := by
  mathlib_model_syntax_guard
example : (0 : ℝ) < 1 := by
  mathlib_retrieval_guard

elab "mathlib_model_code_guard" : tactic => do
  let cfg : ProposeConfig := {
    timeoutSec := 10
    directProbeSec := 0
    candidateProbeSec := 0
    structural := false
    cuts := false
    library := false
    equalityBridge := false
    iffBridge := false
    witnesses := false
    nativeTransforms := false
    nativeCases := false
    frontier := false
    atlasGraph := false
    ai := true
    modelMode := "interactive"
    modelProvider := "replay"
    modelReplayResponse :=
      r#"{"lean_candidates":[{"code":"by norm_num"}]}"#
    experimentalRawLeanCode := true
    modelMaxRounds := 1
  }
  let goal ← getMainGoal
  match ← runSearchWithRouter goal cfg (mathlibRouter cfg) with
  | .solved proof stats =>
      unless stats.modelCalls > 0 do
        throwError "replay model was not called; a fallback masked the model-code path"
      goal.assign proof
      replaceMainGoal []
  | .failed stats =>
      throwError "reviewed model-generated mathlib tactic did not solve the goal; modelCalls={stats.modelCalls}"

/-- The adapter's exact parser capabilities permit an external model to return
real mathlib code; the candidate is validated, executed in isolation, and only
then accepted as a kernel-checkable proof. -/
example : (7 : ℝ) < 11 := by
  mathlib_model_code_guard

/-- The leaf adapter reserves logical structure for ViaLean: the frontier sees
the conjunction, structural search splits it, and mathlib closes both leaves. -/
example (s t : ℝ) (h0 : s = 9 - 2 * t) (h1 : t = 3 * s + 1) :
    And (s = 1) (t = 4) := by
  propose_mathlib (timeoutSec := 10) (directProbeSec := 1) (library := false)
    (cuts := false) (equalityBridge := false)
    (iffBridge := false) (witnesses := false) (nativeTransforms := false)
    (nativeCases := false)

example (s t : ℝ) (h0 : s = 9 - 2 * t) (h1 : t = 3 * s + 1) : s = 1 := by
  propose_mathlib (timeoutSec := 10) (library := false) (frontier := false)
    (structural := false) (cuts := false) (equalityBridge := false)
    (iffBridge := false) (witnesses := false) (nativeTransforms := false)
    (nativeCases := false)
