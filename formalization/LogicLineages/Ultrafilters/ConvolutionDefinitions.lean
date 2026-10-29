module

public import LogicLineages.Ultrafilters.Definitions
public import Mathlib.Topology.Compactification.StoneCech

@[expose] public section
namespace LogicLineages.Ultrafilters

/-- Discrete additive ultrafilter convolution with the source's translation orientation.
No global algebra instance is imposed on ultrafilters. -/
def convolution (p q : Ultrafilter ℝ) : Ultrafilter ℝ :=
  p.bind (fun x => q.map (fun y => x + y))

end LogicLineages.Ultrafilters
