import ViaLean.Solver.Native

namespace ViaLean

structure LeafRouter where
  backends : Array LeafSolver

def LeafRouter.nativeOnly (cfg : ProposeConfig) : LeafRouter :=
  ⟨#[nativeLeafSolver cfg]⟩

end ViaLean
