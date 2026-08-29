import ViaLean.Goal

open Lean Meta

namespace ViaLean

structure PremiseCandidate where
  name   : Name
  score  : Float
  source : String

structure PremiseProvider where
  name     : String
  retrieve : GoalSnapshot → Nat → MetaM (Array PremiseCandidate)

end ViaLean
