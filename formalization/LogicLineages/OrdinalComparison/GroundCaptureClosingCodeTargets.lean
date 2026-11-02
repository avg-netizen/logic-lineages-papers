module
public import LogicLineages.OrdinalComparison.GroundCaptureClosingCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundCaptureClosingCode.Targets

def ExactProtectedSource : Prop := ∀ (Θ Γ : List Ty) (τ : Ty) (t : OriginalTerm (Θ++Γ) τ),
  sourceCode (Γ.map SyntaxCode.typeCode) Θ.length (SyntaxCode.encodeTerm t) =
    SyntaxCode.encodeTerm (t.substitute (GroundClosing.GroundMap.source (protectedMap Θ Γ)))

def ExactOrdinalVector : Prop :=
  (∀ (Γ : List Ty) (q : OrdinalExpression Γ), ordinalCode (Γ.map SyntaxCode.typeCode) (OrdinalSyntax.typedCode q) =
    OrdinalSyntax.typedCode (GroundClosing.expression (UnaryCarrier.groundMap Γ) q)) ∧
  (∀ (Γ : List Ty) (m : Nat) (v : OrdinalVector Γ m),
    vectorCode (Γ.map SyntaxCode.typeCode) (OrdinalSyntax.vectorCode v) =
      OrdinalSyntax.vectorCode (GroundClosing.vector (UnaryCarrier.groundMap Γ) v))

def PrimitiveRecursiveAlgorithms : Prop :=
  Primrec (fun p : List Nat×Nat×Nat => sourceCode p.1 p.2.1 p.2.2) ∧
  Primrec₂ ordinalCode ∧ Primrec₂ vectorCode

/-- The actual canonical ground-capture closing, complete assignment and all
free-ground absence are derived without a supplied result vector. -/
def ActualClosingAssignment : Prop := ∀ (Γ : List Ty) (τ : Ty) (t : OriginalTerm Γ τ),
  ∃ u : OrdinalVector Γ τ.level,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some u ∧
    sourceCode (Γ.map SyntaxCode.typeCode) 0 (SyntaxCode.encodeTerm t) =
      SyntaxCode.encodeTerm (UnaryCarrier.closeGround t) ∧
    DefaultSourceAssignment.assignmentCode (Γ.map SyntaxCode.typeCode)
      (sourceCode (Γ.map SyntaxCode.typeCode) 0 (SyntaxCode.encodeTerm t)) =
      some (vectorCode (Γ.map SyntaxCode.typeCode) (OrdinalSyntax.vectorCode u)) ∧
    ∀ x : Variable Γ .ground,
      (⟨Ty.ground,x⟩ : SourceFreeOccurrences.PackedVariable Γ) ∉
        SourceFreeOccurrences.freeOccurrences (UnaryCarrier.closeGround t)
end LogicLineages.OrdinalComparison.Source.GroundCaptureClosingCode.Targets
