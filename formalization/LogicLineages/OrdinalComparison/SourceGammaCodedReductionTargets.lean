module
public import LogicLineages.OrdinalComparison.SourceGammaCodedReductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaCodedReduction.Targets

def CanonicalQueryAdequacy : Prop := ∀ (G : Nat → Nat) (Γ : List Ty),
  SourceMachineRawValuations.AllGround Γ → ∀ (left right : OriginalTerm Γ .ground),
  (Member G (SourceMachineQueryCode.pack (Γ.length,SyntaxCode.encodeTerm left,SyntaxCode.encodeTerm right)) ↔ Strict G left right)

def ExactNonhalting : Prop := ∀ b e,
  Member (SourceMachineControlNonperiodicity.gamma b) (SourceMachineQueryCode.output b e) ↔
    ¬ SourceBlankMachineSimulation.Halts e

def PrimitiveManyOneReduction : Prop := ∀ b,
  Primrec (SourceMachineQueryCode.output b) ∧
  (∀ e,¬SourceBlankMachineSimulation.Halts e ↔
    Member (SourceMachineControlNonperiodicity.gamma b) (SourceMachineQueryCode.output b e)) ∧
  ManyOneReducible (fun e => ¬SourceBlankMachineSimulation.Halts e)
    (Member (SourceMachineControlNonperiodicity.gamma b))
end LogicLineages.OrdinalComparison.Source.SourceGammaCodedReduction.Targets
