import ViaLean.Scheduler.Basic

namespace ViaLean

/-- UCB1 score used only for ordering attempts; it cannot affect validity. -/
def ucbScore
    (stats : FamilyStats)
    (totalAttempts : Nat)
    (prior exploration priorWeight : Float) : Float :=
  let exploit := stats.meanReward
  let explore := exploration * Float.sqrt
    (Float.log (1.0 + totalAttempts.toFloat) / (1.0 + stats.attempts.toFloat))
  exploit + explore + priorWeight * prior

end ViaLean
