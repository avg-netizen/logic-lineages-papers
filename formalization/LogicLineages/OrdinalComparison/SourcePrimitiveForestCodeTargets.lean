module
public import LogicLineages.OrdinalComparison.SourcePrimitiveForestCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePrimitiveForestCode.Targets
open PrimitiveLowering ExistentialPlan

def ExactPorts : Prop :=
  (∀ (Γ : List Ty) (a : Port Γ), portCode (portNumber a)=SyntaxCode.encodeTerm a.term) ∧
  (∀ (Γ : List Ty) (k : Nat) (a : Port Γ),
    portNumber (portRename (shift k) a)=shiftPort k (portNumber a)) ∧
  (∀ (Γ : List Ty) (i : Fin 9),portNumber (aux (Γ:=Γ) i)=i.val+1)

def ExactExpressions : Prop := ∀ (Γ : List Ty) (e : Expr Γ),
  expressionCode e=SyntaxCode.encodeTerm e.term ∧ expressionCode e=SyntaxCode.encodeTerm e.graph.term

def ExactForests : Prop :=
  (∀ (Γ : List Ty) (a b : Port Γ),eqForest (portNumber a) (portNumber b)=forestCodes (.eq a b)) ∧
  (∀ (Γ : List Ty) (a b c : Port Γ),addForest (portNumber a) (portNumber b) (portNumber c)=forestCodes (.add a b c)) ∧
  (∀ (Γ : List Ty) (a : Port Γ),oneForest (portNumber a)=forestCodes (.one a))

def UniformPrimitiveRecursive : Prop :=
  Primrec₂ shiftPort ∧ Primrec portCode ∧ Primrec successorCode ∧ Primrec₂ eraserCode ∧
  Primrec (fun p : Nat×Nat×Nat×Nat => addPairs p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec unusedPairs ∧ Primrec₂ eqForest ∧
  Primrec (fun p : Nat×Nat×Nat => addForest p.1 p.2.1 p.2.2) ∧ Primrec oneForest
end LogicLineages.OrdinalComparison.Source.SourcePrimitiveForestCode.Targets
