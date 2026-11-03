module
public import LogicLineages.OrdinalComparison.SourceAnnotationCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAnnotationCode.Targets
open ScalarAnnotationData

def ExactOperatorCodec : Prop := ∀ (Γ : List Ty) (op : Operator Γ),
  operatorArity (operatorCode op) = op.arity ∧
  operatorSource (operatorCode op) = SyntaxCode.encodeTerm op.source ∧
  operatorVector (operatorCode op) = OrdinalSyntax.vectorCode op.vector ∧
  operatorHead (operatorCode op) = OrdinalSyntax.typedCode op.head

def ExactErasure : Prop := ∀ (k : Nat) (Γ : List Ty) (F : Variable Γ (Ty.curriedGround (k+1)))
    (d : Tree k Γ F),
  eraseCode (SourceTypedPorts.variableIndex F) (code d) = OrdinalSyntax.typedCode (erase d)

def ExactRepeat : Prop := ∀ (k : Nat) (Γ : List Ty) (F : Variable Γ (Ty.curriedGround (k+1)))
    (count : Nat) (d : Tree k Γ F),
  repeatCode count (code d) = code (SourceAnnotationBuilder.repeatTree count d)

def ExactClosing : Prop :=
  (∀ (Γ : List Ty) (op : Operator (.ground :: Γ)),
    closeOperatorCode (operatorCode op) = operatorCode (closeOperator op)) ∧
  (∀ (k : Nat) (Γ : List Ty) (F : Variable Γ (Ty.curriedGround (k+1)))
    (d : Tree k (.ground :: Γ) (.there F)), closeCode (code d) = code (closeTree d))

def PrimitiveRecursiveAlgorithms : Prop := Primrec₂ eraseCode ∧ Primrec₂ repeatCode ∧
  Primrec closeOperatorCode ∧ Primrec closeCode
end LogicLineages.OrdinalComparison.Source.SourceAnnotationCode.Targets
