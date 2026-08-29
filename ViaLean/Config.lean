import ViaLean.Basic

namespace ViaLean

structure ProposeConfig where
  timeoutSec             : Nat := 10
  directProbeSec         : Nat := 1
  candidateProbeSec      : Nat := 1
  finalDirectMinSec      : Nat := 2
  maxDepth               : Nat := 2
  maxCandidates          : Nat := 12
  maxCandidatesPerFamily : Nat := 4
  maxProposalSize        : Nat := 120
  maxStructuralChildren  : Nat := 6
  structural             : Bool := true
  cuts                   : Bool := true
  equalityBridge         : Bool := true
  iffBridge              : Bool := true
  witnesses              : Bool := true
  library                : Bool := true
  ai                     : Bool := false
  allowTypeCuts          : Bool := false
  ucb                     : Bool := true
  ucbExploration         : Float := 0.8
  ucbPriorWeight         : Float := 0.25
  trace                   : Bool := false
  deterministic          : Bool := true
  nativeMaxDepth         : Nat := 8
  nativeMaxApplications  : Nat := 256

end ViaLean
