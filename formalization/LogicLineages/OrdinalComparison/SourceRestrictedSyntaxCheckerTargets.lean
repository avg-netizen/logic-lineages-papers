module
public import LogicLineages.OrdinalComparison.SourceRestrictedSyntaxCheckerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceRestrictedSyntaxChecker.Targets

def FragmentCalibration : Prop := ∀ (Γ : List Ty) (τ : Ty) (t : OriginalTerm Γ τ),
  fragmentCode (SyntaxCode.encodeTerm t)=true ↔ SourceGroundBinderFragment.Fragment t

def MalformedCases : Prop :=
  (∀ n : Nat, n%8=3 ∨ n%8=4 ∨ n%8=7 → fragmentCode n=false) ∧
  (∀ n : Nat, (n%8=1 ∨ n%8=2) → n/8≠0 → fragmentCode n=false) ∧
  (∀ c : Nat, SourceMachineQueryCode.unpack c=none → restrictedCode c=false)

def ExactSyntaxClass : Prop := ∀ c : Nat,
  restrictedCode c=true ↔ SourceGammaRestrictedReduction.RestrictedSyntax c

def UniformPrimitiveRecursive : Prop := Primrec fragmentCode ∧
  Primrec (fun p : Nat × Nat => groundCode p.1 p.2) ∧ Primrec restrictedCode
end LogicLineages.OrdinalComparison.Source.SourceRestrictedSyntaxChecker.Targets
