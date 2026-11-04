module
public import LogicLineages.OrdinalComparison.SourceMachineQueryCodeDefinitions
public import LogicLineages.OrdinalComparison.SourceMachineRawValuationsDefinitions
public import Mathlib.Computability.Reduce
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaCodedReduction

/-- Independent generic-control strict semantics on successful finite observations
at every positive raw natural valuation. -/
def Strict (G : Nat → Nat) {Γ : List Ty} (left right : OriginalTerm Γ .ground) : Prop :=
  ∀ ν : OrdinalComponent Γ → Nat,(∀ c,0<ν c) →
    ∃ x y : Nat,ParametricSourceEraser.Scalar G (fun c => (ν c : Ordinal)) left x ∧
      ParametricSourceEraser.Scalar G (fun c => (ν c : Ordinal)) right y ∧ x<y

/-- Natural query language with canonical all-ground context. Failed tuple
unpacking or absent actual typed witnesses gives no membership. -/
def Member (G : Nat → Nat) (c : Nat) : Prop :=
  ∃ (n : Nat) (left right : OriginalTerm (List.replicate n Ty.ground) .ground),
    SourceMachineQueryCode.unpack c=some (n,SyntaxCode.encodeTerm left,SyntaxCode.encodeTerm right) ∧
    Strict G left right
end LogicLineages.OrdinalComparison.Source.SourceGammaCodedReduction
