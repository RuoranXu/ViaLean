import ViaLean.Action

namespace ViaLean

structure FamilyStats where
  attempts  : Nat := 0
  rewardSum : Float := 0.0
deriving Inhabited, Repr

def FamilyStats.meanReward (stats : FamilyStats) : Float :=
  if stats.attempts = 0 then 0.0 else stats.rewardSum / stats.attempts.toFloat

structure SchedulerState where
  stats : IO.Ref (Std.HashMap ProposalFamily FamilyStats)

def SchedulerState.create : IO SchedulerState := do
  return ⟨← IO.mkRef {}⟩

def SchedulerState.snapshot (state : SchedulerState) : IO (Std.HashMap ProposalFamily FamilyStats) :=
  state.stats.get

def SchedulerState.record
    (state : SchedulerState) (family : ProposalFamily) (reward : Float) : IO Unit :=
  state.stats.modify fun all =>
    let current := (all.get? family).getD {}
    all.insert family {
      attempts := current.attempts + 1
      rewardSum := current.rewardSum + reward
    }

end ViaLean
