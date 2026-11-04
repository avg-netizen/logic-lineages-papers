module
public import LogicLineages.OrdinalComparison.SourceGammaCodedReductionDefinitions
public import LogicLineages.OrdinalComparison.SourceMachineInternalLevelDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaRestrictedReduction

/-- Independent decoded-query syntax class, not membership in the constructor's image. -/
def RestrictedSyntax (c : Nat) : Prop :=
  ∃ (n : Nat) (left right : OriginalTerm (List.replicate n Ty.ground) .ground),
    SourceMachineQueryCode.unpack c=some (n,SyntaxCode.encodeTerm left,SyntaxCode.encodeTerm right) ∧
    SourceGroundBinderFragment.Fragment left ∧ SourceGroundBinderFragment.Fragment right ∧
    SourceClasses.InternalLevelBound 1 left ∧ SourceClasses.InternalLevelBound 1 right

def Member (G : Nat → Nat) (c : Nat) : Prop := RestrictedSyntax c ∧ SourceGammaCodedReduction.Member G c
end LogicLineages.OrdinalComparison.Source.SourceGammaRestrictedReduction
