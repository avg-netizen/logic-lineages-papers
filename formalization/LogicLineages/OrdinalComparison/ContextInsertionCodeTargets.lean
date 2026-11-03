module
public import LogicLineages.OrdinalComparison.ContextInsertionCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ContextInsertionCode.Targets
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def ExactSourceInsertion : Prop := ∀ (Θ Δ Γ : List Ty) (τ : Ty) (t : OriginalTerm (Θ++Γ) τ),
  sourceCode Θ.length Δ.length (SyntaxCode.encodeTerm t) =
    SyntaxCode.encodeTerm (t.rename (insertion Θ Δ Γ))

def ExactOrdinalVector : Prop :=
  (∀ (Θ Δ Γ : List Ty) (q : OrdinalExpression (Θ++Γ)),
    ordinalCode Θ.length Δ.length (OrdinalSyntax.typedCode q) =
      OrdinalSyntax.typedCode (ordinalExpressionRename (insertion Θ Δ Γ) q)) ∧
  (∀ (Θ Δ Γ : List Ty) (m : Nat) (v : OrdinalVector (Θ++Γ) m),
    vectorCode Θ.length Δ.length (OrdinalSyntax.vectorCode v) =
      OrdinalSyntax.vectorCode (SourceRenaming.renameVector (insertion Θ Δ Γ) v))

def PrimitiveRecursiveAlgorithms : Prop :=
  Primrec (fun p : Nat×Nat×Nat => sourceCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat×Nat×Nat => ordinalCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat×Nat×List Nat => vectorCode p.1 p.2.1 p.2.2)

/-- Actual source renaming commutes with the complete assignment, including
scalar, with no semantic equality assumption on private functional values. -/
def ActualInsertedAssignment : Prop := ∀ (Θ Δ Γ : List Ty) (τ : Ty) (t : OriginalTerm (Θ++Γ) τ),
  ∃ u : OrdinalVector (Θ++Γ) τ.level,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some u ∧
    DefaultSourceAssignment.assignmentCode ((Θ++(Δ++Γ)).map SyntaxCode.typeCode)
      (sourceCode Θ.length Δ.length (SyntaxCode.encodeTerm t)) =
        some (vectorCode Θ.length Δ.length (OrdinalSyntax.vectorCode u))
end LogicLineages.OrdinalComparison.Source.ContextInsertionCode.Targets
