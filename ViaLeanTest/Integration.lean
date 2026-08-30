import ViaLean

open Lean Meta Elab Tactic ViaLean

theorem vialeanRetrievedTrans (P Q R : Prop)
    (pq : P → Q) (qr : Q → R) : P → R := fun p => qr (pq p)

elab "library_replay_guard" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let snap ← snapshot goal
    let cfg : ProposeConfig := {
      directProbeSec := 0
      candidateProbeSec := 0
      structural := false
      cuts := false
      library := false
      nativeTransforms := false
      nativeCases := false
      maxDepth := 3
    }
    let proposals ← libraryCutProposals snap cfg #[{
      name := ``vialeanRetrievedTrans
      score := 1.0
      source := "regression"
    }]
    let proposal? := proposals.find? fun proposal =>
      match proposal.payload with
      | .libraryApply name => name == ``vialeanRetrievedTrans
      | _ => false
    let some proposal := proposal?
      | throwError "library proposer discarded the retrieved theorem name"
    let some proof ← runManualProposal goal cfg proposal
      | throwError "retrieved theorem could not be replayed"
    goal.assign proof
    replaceMainGoal []

example (P Q R : Prop) (pq : P → Q) (qr : Q → R) : P → R := by
  library_replay_guard

elab "solve_stats_guard" : tactic => do
  let goal ← getMainGoal
  let cfg : ProposeConfig := {
    timeoutSec := 5
    directProbeSec := 0
    candidateProbeSec := 0
    structural := false
    cuts := false
    library := false
    iffBridge := false
    witnesses := false
    nativeTransforms := false
    nativeCases := false
    maxDepth := 3
  }
  match ← runSearch goal cfg with
  | .failed stats => throwError "stats regression search failed after {stats.proposalAttempts} proposals"
  | .solved proof stats =>
      unless stats.proposalAttempts > 0 && stats.bridgeDepth > 0 &&
          stats.winningFamily? == some .equalityLocal do
        throwError "SolveStats were not populated by the winning search"
      goal.assign proof
      replaceMainGoal []

example (α : Type) (a b c : α) (h₁ : a = b) (h₂ : b = c) : a = c := by
  solve_stats_guard

elab "persistent_scheduler_guard" : tactic => do
  let goal ← getMainGoal
  let scheduler ← SchedulerState.create
  let persisted : PersistentStats := {
    families := #[{ family := "direct", attempts := 7, rewardSum := 3.5 }]
  }
  persisted.seedScheduler scheduler
  let seeded ← scheduler.snapshot
  let direct := (seeded.get? .direct).getD {}
  unless direct.attempts == 7 && direct.rewardSum == 3.5 do
    throwError "persistent scheduler seed was not applied"
  scheduler.record .direct 1.0
  let exported ← scheduler.toPersistentStats
  unless exported.families.any fun stats =>
      stats.family == "direct" && stats.attempts == 8 && stats.rewardSum == 4.5 do
    throwError "scheduler aggregate was not exported"
  goal.assign (mkConst ``True.intro)
  replaceMainGoal []

example : True := by
  persistent_scheduler_guard

elab "bounded_process_guard" : tactic => do
  let goal ← getMainGoal
  let executable ← IO.appPath
  match ← runBoundedProcess executable.toString #["--version"] "" 5000 1 with
  | .ok _ => throwError "model process output limit was not enforced"
  | .error message =>
      unless message.contains "exceeds 1 characters" do
        throwError "unexpected bounded-process error: {message}"
  goal.assign (mkConst ``True.intro)
  replaceMainGoal []

example : True := by
  bounded_process_guard
