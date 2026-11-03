module
public import LogicLineages.OrdinalComparison.TrackedSourceInspectionCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.TrackedSourceInspectionCode.Targets
open SourceFreeOccurrences

def ExactFreeOccurrence : Prop := ∀ (Γ : List Ty) (σ τ : Ty) (F : Variable Γ σ)
    (t : OriginalTerm Γ τ),
  occursCode (SourceTypedPorts.variableIndex F) (SyntaxCode.encodeTerm t) = true ↔
    (⟨σ,F⟩ : PackedVariable Γ) ∈ freeOccurrences t

def ExactArity : Prop := ∀ (τ : Ty) (n : Nat),
  arityCode (SyntaxCode.typeCode τ) = some n ↔ τ = Ty.curriedGround n

def PrimitiveRecursiveAlgorithms : Prop := Primrec₂ occursCode ∧ Primrec arityCode

/-- Every unchanged grammar witness is inspected from its actual erased source;
no assertion that distinct witnesses produce identical annotation data. -/
def ActualGrammarInspection : Prop := ∀ (k : Nat) (Γ : List Ty)
    (F : Variable Γ (Ty.curriedGround (k+1))) (n : Nat) (e : TrackedSource.Expr k Γ F n),
  occursCode (SourceTypedPorts.variableIndex F) (SyntaxCode.encodeTerm (TrackedSource.erase e)) =
      TrackedSource.active e ∧
  SyntaxCode.check (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm (TrackedSource.erase e)) =
      some (SyntaxCode.typeCode (Ty.curriedGround n)) ∧
  arityCode (SyntaxCode.typeCode (Ty.curriedGround n)) = some n
end LogicLineages.OrdinalComparison.Source.TrackedSourceInspectionCode.Targets
