module
public import LogicLineages.OrdinalComparison.ParametricLiteralWeakWrapperDefinitions
public import LogicLineages.OrdinalComparison.SourceMachineInternalLevelDefinitions
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceLiteralWeakWrapperCode
def identityCode (a : Nat) : Nat := 8*Nat.pair 6 a+5
def constantCode (a : Nat) : Nat := 8*Nat.pair (8*Nat.pair 0 1+6) a+5
end LogicLineages.OrdinalComparison.Source.SourceLiteralWeakWrapperCode
