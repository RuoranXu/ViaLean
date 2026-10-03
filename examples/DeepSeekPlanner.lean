import ViaLean

open ViaLean

/-- A conservative hosted-model profile for persistent planner co-search.
The API key is read from `VIALEAN_API_KEY`; it is never embedded in Lean source. -/
macro "propose_deepseek" : tactic =>
  `(tactic|
    propose
      (ai := true)
      (modelMode := "planner")
      (modelProvider := "openai-compatible")
      (modelEndpoint := "https://api.deepseek.com/chat/completions")
      (modelName := "deepseek-flash")
      (modelApiKeyEnv := "VIALEAN_API_KEY")
      (modelJsonMode := true)
      (modelReasoningEffort := "high")
      (modelMaxTokens := 8192)
      (modelTimeoutMs := 120000)
      (timeoutSec := 180)
      (plannerMaxCalls := 3)
      (plannerMaxPayloadChars := 24000)
      (trace := true))

/-
After setting `VIALEAN_API_KEY` outside the source tree:

example {alpha : Type} (a b : alpha) (h : a = b) : b = a := by
  propose_deepseek
-/
