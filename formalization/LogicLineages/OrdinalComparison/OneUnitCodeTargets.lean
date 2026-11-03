module
public import LogicLineages.OrdinalComparison.OneUnitCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OneUnitCode.Targets

def ExactLiteralSyntax : Prop :=
  (∀ (Γ : List Ty) (τ : Ty) (a : OriginalTerm Γ τ),
    unusedCode (SyntaxCode.encodeTerm a) = SyntaxCode.encodeTerm (OneUnit.unused a)) ∧
  (∀ (Γ : List Ty) (σ τ : Ty) (a : OriginalTerm (σ::Γ) τ),
    firstCode (SyntaxCode.typeCode σ) (SyntaxCode.encodeTerm a) = SyntaxCode.encodeTerm (OneUnit.first a) ∧
    secondCode (SyntaxCode.typeCode σ) (SyntaxCode.encodeTerm a) = SyntaxCode.encodeTerm (OneUnit.second a)) ∧
  ∀ (τ : Ty) (d : OneUnit.Data),
    coefficientCode (SyntaxCode.typeCode τ) = OneUnit.coefficient τ ∧
    constantCode (SyntaxCode.typeCode τ) d.d' = OneUnit.constant τ d

def ExactCompiler : Prop :=
  (∀ (Γ : List Ty) (σ : Ty) (m : Nat) (h : OrdinalVector (σ::Γ) m),
    multiplierCode (SyntaxCode.typeCode σ) (OrdinalSyntax.vectorCode h) = OneUnit.multiplier h) ∧
  ∀ (Γ : List Ty) (σ τ : Ty) (a : OriginalTerm (σ::Γ) τ),
    compileCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.typeCode σ) (SyntaxCode.encodeTerm a) =
      (OneUnit.compile a).map dataCode

def PrimitiveRecursiveAlgorithms : Prop :=
  Primrec unusedCode ∧ Primrec₂ firstCode ∧ Primrec₂ secondCode ∧
  Primrec₂ multiplierCode ∧
  Primrec (fun p : List Nat×Nat×Nat => compileCode p.1 p.2.1 p.2.2) ∧
  Primrec coefficientCode ∧ Primrec₂ constantCode

/-- Success and the real full-vector coefficients are inherited from the
original source theorem, not supplied as an effectiveness premise. -/
def ActualCompilerTotality : Prop := ∀ (Γ : List Ty) (σ τ : Ty) (a : OriginalTerm (σ::Γ) τ),
  ∃ d : OneUnit.Data,
    OneUnit.compile a = some d ∧
    compileCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.typeCode σ) (SyntaxCode.encodeTerm a) = some (dataCode d) ∧
    0 < d.d ∧ (d.free = false → d.d < d.d')
end LogicLineages.OrdinalComparison.Source.OneUnitCode.Targets
