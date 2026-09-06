import ViaLean.Basic

namespace ViaLean

inductive RankingMode
  | prior
  | ucb
  | planner
  | hybrid
deriving BEq, Repr, Inhabited

structure ProposeConfig where
  timeoutSec             : Nat := 10
  directProbeSec         : Nat := 1
  candidateProbeSec      : Nat := 1
  finalDirectMinSec      : Nat := 2
  maxDepth               : Nat := 2
  maxCandidates          : Nat := 12
  maxRetrievedPremises   : Nat := 12
  maxActionsPerNode      : Nat := 32
  maxCandidatesPerFamily : Nat := 4
  maxProposalSize        : Nat := 120
  localSynthDepth          : Nat := 3
  localSynthMaxTerms       : Nat := 64
  localSynthMaxGaps        : Nat := 24
  maxStructuralChildren  : Nat := 6
  structural             : Bool := true
  cuts                   : Bool := true
  equalityBridge         : Bool := true
  iffBridge              : Bool := true
  witnesses              : Bool := true
  library                : Bool := true
  ai                     : Bool := false
  modelMode               : String := "planner"
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
  experimentalRawLeanCode : Bool := false
  plannerMaxPayloadChars  : Nat := 16000
  plannerMaxCalls         : Nat := 4
  plannerMinReplanGain    : Float := 0.1
  plannerAllowExpansion   : Bool := true
  plannerUncertaintyThreshold : Float := 0.45
  plannerFailureReplanCount : Nat := 2
  plannerMinNewNodes       : Nat := 1
  plannerMinNewTransitions : Nat := 2
  allowTypeCuts          : Bool := false
  ucb                     : Bool := true
  ucbExploration         : Float := 0.8
  ucbPriorWeight         : Float := 0.25
  persistentStatsPath    : String := ""
  trace                   : Bool := false
  traceJsonlPath          : String := ""
  traceMaxEvents          : Nat := 4096
  deterministic          : Bool := true
  rankingMode             : RankingMode := .prior
  stableTieBreak          : Bool := true
  nativeMaxDepth         : Nat := 8
  nativeMaxApplications  : Nat := 256
  nativeTransforms        : Bool := true
  nativeCases             : Bool := true
  nativeMaxCaseBranches   : Nat := 6
  frontier                : Bool := true
  atlasGraph              : Bool := true
  frontierMaxProbes       : Nat := 32
  frontierMaxPerPerspective : Nat := 4
  frontierMaxChildren     : Nat := 6
  frontierMaxFacts        : Nat := 12
  frontierForwardDepth    : Nat := 2
  frontierContextChars    : Nat := 16000
  frontierFutureDepth     : Nat := 3
  frontierFutureWidth     : Nat := 6
  frontierFutureNodes     : Nat := 24
  atlasMaxNodes           : Nat := 96
  atlasMaxTransitions     : Nat := 160
  atlasMaxWorkUnits       : Nat := 256
  atlasMaxMetaOps         : Nat := 256
  atlasMaxRenderedChars   : Nat := 16000
  atlasMaxRegions         : Nat := 12
  atlasRareStrategyReserve : Nat := 1
  atlasGuaranteedWork      : Nat := 96
  atlasAdaptiveWork        : Nat := 96
  atlasNeuralWork          : Nat := 64
  atlasExpansionMaxDepth   : Nat := 6
  atlasExpansionMaxWidth   : Nat := 8

end ViaLean
