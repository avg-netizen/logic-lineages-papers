module
public import LogicLineages.OrdinalComparison.SourceGammaWeakCodedReductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaWeakCodedReduction.Targets

def CanonicalAdequacy : Prop := ∀ (G : Nat → Nat) (Γ : List Ty),
  SourceMachineRawValuations.AllGround Γ → ∀ (left right : OriginalTerm Γ .ground),
  (RawMember G (SourceMachineQueryCode.pack (Γ.length,SyntaxCode.encodeTerm left,SyntaxCode.encodeTerm right)) ↔
    Weak G left right)

def ExactGeneratedQuery : Prop := ∀ b e : Nat,
  request b e=((ExistentialPlan.compile (SourceMachineConjunctionPlan.plan b e)).context.length,
    SyntaxCode.encodeTerm (ParametricLiteralWeakWrapper.constantApply (SourceMachineAggregateBridge.aggregate b e).2),
    SyntaxCode.encodeTerm (ParametricLiteralWeakWrapper.identityApply (SourceMachineAggregateBridge.aggregate b e).1)) ∧
  SourceGammaRestrictedReduction.RestrictedSyntax (output b e)

def UniformPrimitiveRecursive : Prop := Primrec₂ request ∧ Primrec₂ output

def FixedNonhaltingReduction : Prop := ∀ b : Nat,
  (∀ e : Nat, Member (SourceMachineControlNonperiodicity.gamma b) (output b e) ↔
    ¬SourceBlankMachineSimulation.Halts e) ∧
  ManyOneReducible (fun e => ¬SourceBlankMachineSimulation.Halts e)
    (Member (SourceMachineControlNonperiodicity.gamma b))
end LogicLineages.OrdinalComparison.Source.SourceGammaWeakCodedReduction.Targets
