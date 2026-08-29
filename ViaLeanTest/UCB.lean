import ViaLean

open ViaLean

run_meta
  let fresh : FamilyStats := { attempts := 0, rewardSum := 0.0 }
  let explored : FamilyStats := { attempts := 20, rewardSum := 0.0 }
  let freshScore := ucbScore fresh 20 0.5 0.8 0.25
  let exploredScore := ucbScore explored 20 0.5 0.8 0.25
  unless freshScore > exploredScore do
    throwError "UCB exploration bonus should decrease as attempts grow"
