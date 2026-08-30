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
  modelMode               : String := "policy"
  modelProvider          : String := "none"
  modelCommand           : String := ""
  modelCommandArgsJson   : String := "[]"
  modelReplayResponse    : String := ""
  modelEndpoint          : String := "http://127.0.0.1:11434/v1/chat/completions"
  modelName              : String := ""
  modelApiKeyEnv         : String := "VIALEAN_API_KEY"
  modelCurlCommand       : String := "curl"
  modelTimeoutMs         : Nat := 1500
  modelMaxSignals        : Nat := 16
  modelMaxTokens         : Nat := 512
  modelMaxResponseChars  : Nat := 65536
  modelContextChars      : Nat := 12000
  modelTemperature       : Float := 0.0
  modelWeight            : Float := 0.65
  modelMaxRounds          : Nat := 4
  modelMaxFeedbackEvents  : Nat := 48
  modelLeanCode           : Bool := true
  modelMaxCodeCandidates  : Nat := 4
  modelMaxCodeChars       : Nat := 12000
  modelCodeMaxHeartbeats  : Nat := 50000
  allowTypeCuts          : Bool := false
  ucb                     : Bool := true
  ucbExploration         : Float := 0.8
  ucbPriorWeight         : Float := 0.25
  persistentStatsPath    : String := ""
  trace                   : Bool := false
  deterministic          : Bool := true
  nativeMaxDepth         : Nat := 8
  nativeMaxApplications  : Nat := 256
  nativeTransforms        : Bool := true
  nativeCases             : Bool := true
  nativeMaxCaseBranches   : Nat := 6
  frontier                : Bool := true
  frontierMaxProbes       : Nat := 32
  frontierMaxPerPerspective : Nat := 4
  frontierMaxChildren     : Nat := 6
  frontierMaxFacts        : Nat := 12
  frontierForwardDepth    : Nat := 2
  frontierContextChars    : Nat := 16000
  frontierFutureDepth     : Nat := 3
  frontierFutureWidth     : Nat := 6
  frontierFutureNodes     : Nat := 24

end ViaLean
