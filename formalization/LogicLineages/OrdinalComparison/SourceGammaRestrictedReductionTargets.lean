module
public import LogicLineages.OrdinalComparison.SourceGammaRestrictedReductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaRestrictedReduction.Targets

def ExactSyntaxClass : Prop := ∀ (Γ : List Ty),SourceMachineRawValuations.AllGround Γ →
  ∀ (left right : OriginalTerm Γ .ground),
  (RestrictedSyntax (SourceMachineQueryCode.pack (Γ.length,SyntaxCode.encodeTerm left,SyntaxCode.encodeTerm right)) ↔
    SourceGroundBinderFragment.Fragment left ∧ SourceGroundBinderFragment.Fragment right ∧
    SourceClasses.InternalLevelBound 1 left ∧ SourceClasses.InternalLevelBound 1 right)

def GeneratedRange : Prop := ∀ b e,RestrictedSyntax (SourceMachineQueryCode.output b e)

def RestrictedManyOneReduction : Prop := ∀ b,
  Primrec (SourceMachineQueryCode.output b) ∧
  (∀ e,¬SourceBlankMachineSimulation.Halts e ↔
    Member (SourceMachineControlNonperiodicity.gamma b) (SourceMachineQueryCode.output b e)) ∧
  ManyOneReducible (fun e => ¬SourceBlankMachineSimulation.Halts e)
    (Member (SourceMachineControlNonperiodicity.gamma b))
end LogicLineages.OrdinalComparison.Source.SourceGammaRestrictedReduction.Targets
