module
public import LogicLineages.OrdinalComparison.SourceLiteralWeakWrapperCodeDefinitions
public import LogicLineages.OrdinalComparison.SourceGammaRestrictedReductionDefinitions
public import LogicLineages.OrdinalComparison.SourceGammaLiteralWeakAggregateDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaWeakCodedReduction

def Weak (G : Nat → Nat) {Γ : List Ty} (left right : OriginalTerm Γ .ground) : Prop :=
  ∀ ν : OrdinalComponent Γ → Nat, (∀ c,0<ν c) →
    ∃ x y : Nat, ParametricSourceEraser.Scalar G (fun c => (ν c : Ordinal)) left x ∧
      ParametricSourceEraser.Scalar G (fun c => (ν c : Ordinal)) right y ∧ x ≤ y

def RawMember (G : Nat → Nat) (code : Nat) : Prop :=
  ∃ (n : Nat) (left right : OriginalTerm (List.replicate n Ty.ground) .ground),
    SourceMachineQueryCode.unpack code=some (n,SyntaxCode.encodeTerm left,SyntaxCode.encodeTerm right) ∧
    Weak G left right

def Member (G : Nat → Nat) (code : Nat) : Prop :=
  SourceGammaRestrictedReduction.RestrictedSyntax code ∧ RawMember G code

def request (b e : Nat) : SourceMachineQueryCode.Query :=
  let q := SourceMachineQueryCode.request b e
  (q.1,SourceLiteralWeakWrapperCode.constantCode q.2.1,
    SourceLiteralWeakWrapperCode.identityCode q.2.2)
def output (b e : Nat) : Nat := SourceMachineQueryCode.pack (request b e)
end LogicLineages.OrdinalComparison.Source.SourceGammaWeakCodedReduction
