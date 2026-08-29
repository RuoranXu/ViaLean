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
  allowTypeCuts          : Bool := false
  ucb                     : Bool := true
  ucbExploration         : Float := 0.8
  ucbPriorWeight         : Float := 0.25
  trace                   : Bool := false
  deterministic          : Bool := true
  nativeMaxDepth         : Nat := 8
  nativeMaxApplications  : Nat := 256

end ViaLean
