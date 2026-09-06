import ViaLean

open Lean Meta Elab Tactic ViaLean

/-!
This is a dependency-free replay slice adapted from theorem statements in the
Lean 4 Init/Std sources shipped with the active toolchain.  It exercises the
same statement shapes without importing mathlib or referring to their proofs.
The source declaration names are recorded above each case.
-/

-- Nat.succ_ne_zero, Init/Data/Nat/Basic.lean
example (n : Nat) : Not (Nat.succ n = 0) := by
  propose (timeoutSec := 8)

-- List.append_nil, Init/Data/List/Basic.lean
example {A : Type} (xs : List A) : xs ++ [] = xs := by
  propose (timeoutSec := 8)

-- List.mem_cons_self, Init/Data/List/Lemmas.lean
example {A : Type} (a : A) (xs : List A) : List.Mem a (a :: xs) := by
  propose (timeoutSec := 8)

-- Array.reverse_reverse, Init/Data/Array/Lemmas.lean
example {A : Type} (xs : Array A) : xs.reverse.reverse = xs := by
  propose (timeoutSec := 8)

-- BitVec.mul_zero, Init/Data/BitVec/Lemmas.lean
example {w : Nat} (x : BitVec w) : x * 0#w = 0#w := by
  propose (timeoutSec := 8)

-- String.length_append, Init/Data/String/Basic.lean
example (s t : String) : (s ++ t).length = s.length + t.length := by
  propose (timeoutSec := 8)

#guard matchedComputeModes.size == 8

elab "matched_compute_replay_guard" : tactic => do
  getMainGoal >>= fun goal =>
    goal.withContext do
      let base : ProposeConfig := {
        timeoutSec := 3
        directProbeSec := 0
        finalDirectMinSec := 0
        localSynthMaxTerms := 0
        localSynthMaxGaps := 0
        atlasMaxWorkUnits := 48
        atlasMaxMetaOps := 48
        atlasGuaranteedWork := 12
        atlasAdaptiveWork := 12
        atlasNeuralWork := 12
      }
      let falseType := mkConst (Name.mkSimple "False")
      mkArrow falseType falseType >>= fun target =>
        runMatchedComputeCase "std.not_false" target base >>= fun results => do
          unless results.size == matchedComputeModes.size do
            throwError "matched-compute ablation omitted a mode"
          unless results.all (fun result => result.solved) do
            throwError "matched-compute replay failed: {repr results}"
          let some native := results.find? (fun result => result.mode == .nativeOnly)
            | throwError "native baseline missing"
          let some flat := results.find? (fun result => result.mode == .flatFrontier)
            | throwError "flat frontier baseline missing"
          let some graph := results.find? (fun result => result.mode == .graphAtlas)
            | throwError "graph Atlas baseline missing"
          let some policy := results.find? (fun result => result.mode == .atlasPolicy)
            | throwError "policy ablation missing"
          let some value := results.find? (fun result => result.mode == .atlasPolicyValue)
            | throwError "value ablation missing"
          let some expansion := results.find? (fun result => result.mode == .plannerExpansion)
            | throwError "expansion ablation missing"
          let some raw := results.find? (fun result => result.mode == .interactiveRaw)
            | throwError "interactive raw baseline missing"
          unless native.modelCalls == 0 && flat.modelCalls > 0 &&
              graph.atlasTransitions > 0 && policy.modelCalls > 0 &&
              value.modelCalls > 0 && value.replanCount > 0 &&
              expansion.modelCalls > 0 && expansion.replanCount > 0 &&
              raw.modelCalls > 0 do
            throwError "an ablation mode was nominal rather than active: {repr results}"
      goal.assign (mkConst (Name.str (Name.mkSimple "True") "intro"))
      replaceMainGoal []

example : True := by
  matched_compute_replay_guard
