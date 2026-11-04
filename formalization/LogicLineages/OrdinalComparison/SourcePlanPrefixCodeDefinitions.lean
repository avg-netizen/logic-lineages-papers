module
public import LogicLineages.OrdinalComparison.SourcePrimitiveForestCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePlanPrefixCode

def shiftPair (k : Nat) (p : Nat×Nat) : Nat×Nat :=
  (ContextInsertionCode.sourceCode 0 k p.1,ContextInsertionCode.sourceCode 0 k p.2)
def shiftPairs (k : Nat) (ps : List (Nat×Nat)) : List (Nat×Nat) := ps.map (shiftPair k)
end LogicLineages.OrdinalComparison.Source.SourcePlanPrefixCode
