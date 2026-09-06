import ViaLean.Action

open Lean

namespace ViaLean

/-- Coarse strategy identity shared by producers, the Atlas, scheduler and planner. -/
inductive StrategyFamily
  | normalization | contradiction | equality | elimination | construction
  | backward | forward | witness | cut | structural | leaf | mixed
deriving BEq, Hashable, Repr, Inhabited

/-- Executable symbolic operations. Expressions and local ids never cross the model boundary. -/
inductive SymbolicOperation
  | exactTerm (term : Expr)
  | exactLocal (fvar : FVarId)
  | applyLocal (fvar : FVarId)
  | applyConst (name : Name)
  | intro
  | constructor (name : Name)
  | casesLocal (fvar : FVarId)
  | rewriteLocal (fvar : FVarId) (symm : Bool)
  | simplifyTarget
  | contradiction
  | equalityBridge (mid : Expr)
  | iffBridge (mid : Expr)
  | witness (value : Expr)
  | cut (type : Expr)
  | structural (rule : StructuralRule)
  | leaf (solver : SolverKind)
  | sketch (holes : Array Expr)
deriving Inhabited

inductive TransitionOrigin
  | local | library (name : Name) | model | normalization | derived | replay
deriving BEq, Hashable, Repr, Inhabited

structure SymbolicTransitionCandidate where
  operation : SymbolicOperation
  family : StrategyFamily
  prior : Float := 0.5
  estimatedCost : Float := 1.0
  origin : TransitionOrigin := .derived
  fingerprint : UInt64
deriving Inhabited

def ProposalFamily.toStrategyFamily : ProposalFamily → StrategyFamily
  | .direct => .leaf
  | .structural => .structural
  | .localCut | .libraryCut | .externalCut => .cut
  | .equalityNormalize | .equalityLocal | .equalityExternal => .equality
  | .witnessLocal | .witnessExternal => .witness

def StrategyFamily.name : StrategyFamily → String
  | .normalization => "normalization"
  | .contradiction => "contradiction"
  | .equality => "equality"
  | .elimination => "elimination"
  | .construction => "construction"
  | .backward => "backward"
  | .forward => "forward"
  | .witness => "witness"
  | .cut => "cut"
  | .structural => "structural"
  | .leaf => "leaf"
  | .mixed => "mixed"

def StrategyFamily.ofName? (name : String) : Option StrategyFamily :=
  match name.trimAscii.toString.toLower with
  | "normalization" => some .normalization
  | "contradiction" | "consistency" => some .contradiction
  | "equality" | "rewrite" => some .equality
  | "elimination" | "cases" => some .elimination
  | "construction" | "constructor" => some .construction
  | "backward" | "apply" => some .backward
  | "forward" => some .forward
  | "witness" => some .witness
  | "cut" | "helper" => some .cut
  | "structural" | "intro" => some .structural
  | "leaf" | "direct" => some .leaf
  | "mixed" => some .mixed
  | _ => none

def SymbolicOperation.name : SymbolicOperation → String
  | .exactTerm _ => "exact_term"
  | .exactLocal _ => "exact_local"
  | .applyLocal _ => "apply_local"
  | .applyConst name => s!"apply_const:{name}"
  | .intro => "intro"
  | .constructor name => s!"constructor:{name}"
  | .casesLocal _ => "cases_local"
  | .rewriteLocal _ false => "rewrite_local"
  | .rewriteLocal _ true => "rewrite_local_reverse"
  | .simplifyTarget => "simplify_target"
  | .contradiction => "contradiction"
  | .equalityBridge _ => "equality_bridge"
  | .iffBridge _ => "iff_bridge"
  | .witness _ => "witness"
  | .cut _ => "cut"
  | .structural rule => s!"structural:{(repr rule).pretty}"
  | .leaf solver => s!"leaf:{(repr solver).pretty}"
  | .sketch holes => s!"sketch:{holes.size}"

private def ProposalOrigin.toTransitionOrigin : ProposalOrigin → TransitionOrigin
  | .local | .manual => .local
  | .library name => .library name
  | .external | .planner => .model
  | .normalization => .normalization
  | .derived => .derived

def ProofAction.toSymbolic : ProofAction → SymbolicTransitionCandidate
  | action@{ payload := .close solver, .. } => {
      operation := .leaf solver, family := action.family.toStrategyFamily
      prior := action.prior, estimatedCost := action.estimatedCost
      fingerprint := action.fingerprint }
  | action@{ payload := .structural rule, .. } => {
      operation := .structural rule, family := action.family.toStrategyFamily
      prior := action.prior, estimatedCost := action.estimatedCost
      fingerprint := action.fingerprint }
  | action@{ payload := .sketch holes, .. } => {
      operation := .sketch holes, family := .mixed
      prior := action.prior, estimatedCost := action.estimatedCost
      fingerprint := action.fingerprint }
  | action@{ payload := .proposal proposal, .. } => {
      operation := match proposal.payload with
        | .directTerm term => .exactTerm term
        | .cutType type => .cut type
        | .libraryApply name => .applyConst name
        | .equalityMid mid => .equalityBridge mid
        | .iffMid mid => .iffBridge mid
        | .witness value => .witness value
        | .structural rule => .structural rule
      family := action.family.toStrategyFamily
      prior := action.prior
      estimatedCost := action.estimatedCost
      origin := proposal.origin.toTransitionOrigin
      fingerprint := action.fingerprint }

end ViaLean
