module
public import LogicLineages.OrdinalComparison.SourceScalingSpineCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceBinaryHalvingTrace
open SourceAdditionCompletion
abbrev TraceState := Nat × List Nat
/-- Parities are prepended: after termination the list is inner-to-outer. -/
def advance (s : TraceState) : TraceState :=
  if s.1<2 then s else (s.1/2,(s.1%2)::s.2)
def trace (k : Nat) : TraceState := advance^[k] (k,[])
def wrap (d : BinaryDAG) (bit : Nat) : BinaryDAG :=
  if bit=0 then .double d else .doubleOne d
def reconstruct (s : TraceState) : BinaryDAG :=
  s.2.foldl wrap (if s.1=0 then .zero else .one)
end LogicLineages.OrdinalComparison.Source.SourceBinaryHalvingTrace
