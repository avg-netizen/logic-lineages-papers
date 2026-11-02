module
public import LogicLineages.OrdinalComparison.SelectedBinderCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SelectedBinderCode.Targets

def ExactSourcePermutation : Prop := ∀ (Θ left right : List Ty) (σ τ : Ty)
    (t : OriginalTerm (Θ++(left++σ::right)) τ),
  sourceCode Θ.length left.length (SyntaxCode.encodeTerm t) =
    SyntaxCode.encodeTerm (t.rename (permutation Θ left right σ))

def ExactOrdinalVectorPermutation : Prop :=
  (∀ (Θ left right : List Ty) (σ : Ty) (q : OrdinalExpression (Θ++(left++σ::right))),
    ordinalCode Θ.length left.length (OrdinalSyntax.typedCode q) =
      OrdinalSyntax.typedCode (ordinalExpressionRename (permutation Θ left right σ) q)) ∧
  (∀ (Θ left right : List Ty) (σ : Ty) (m : Nat) (v : OrdinalVector (Θ++(left++σ::right)) m),
    vectorCode Θ.length left.length (OrdinalSyntax.vectorCode v) =
      OrdinalSyntax.vectorCode (SourceRenaming.renameVector (permutation Θ left right σ) v))

def PrimitiveRecursiveAlgorithms : Prop :=
  Primrec (fun p : Nat×Nat×Nat => indexCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat×Nat×Nat => sourceCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat×Nat×Nat => ordinalCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat×Nat×List Nat => vectorCode p.1 p.2.1 p.2.2)

/-- The full original source assignment is derived, and the numeric vector
map is the actual assignment of the capture-avoiding permuted source. -/
def ActualPermutedAssignment : Prop := ∀ (Θ left right : List Ty) (σ τ : Ty)
    (t : OriginalTerm (Θ++(left++σ::right)) τ),
  ∃ u : OrdinalVector (Θ++(left++σ::right)) τ.level,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some u ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (t.rename (permutation Θ left right σ)) =
      some (SourceRenaming.renameVector (permutation Θ left right σ) u) ∧
    DefaultSourceAssignment.assignmentCode ((Θ++(σ::(left++right))).map SyntaxCode.typeCode)
      (sourceCode Θ.length left.length (SyntaxCode.encodeTerm t)) =
      some (vectorCode Θ.length left.length (OrdinalSyntax.vectorCode u))
end LogicLineages.OrdinalComparison.Source.SelectedBinderCode.Targets
