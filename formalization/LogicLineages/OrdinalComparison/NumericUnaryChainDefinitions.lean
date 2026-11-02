module
public import LogicLineages.OrdinalComparison.ContextInsertionCodeDefinitions
public import LogicLineages.OrdinalComparison.HeterogeneousUnaryAssemblyDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.NumericUnaryChain

abbrev RawOperator := List Nat×Nat×List Nat
abbrev RawPair := Nat×List Nat

def operatorCode {Γ} (op : HeterogeneousUnaryAssembly.Operator Γ) : RawOperator :=
  (op.privateContext.map SyntaxCode.typeCode,SyntaxCode.encodeTerm op.term,OrdinalSyntax.vectorCode op.vector)

def pairCode {Γ} (p : OriginalTerm Γ (Ty.curriedGround 1)×OrdinalVector Γ 1) : RawPair :=
  (SyntaxCode.encodeTerm p.1,OrdinalSyntax.vectorCode p.2)

def shiftPair (depth count : Nat) (p : RawPair) : RawPair :=
  (ContextInsertionCode.sourceCode depth count p.1,ContextInsertionCode.vectorCode depth count p.2)

/-- Private prefixes are kept occurrence-by-occurrence; Γ stays shared. -/
def contextCode (Γ : List Nat) (ops : List RawOperator) : List Nat :=
  ops.foldr (fun op tail => op.1++tail) Γ

/-- The first coordinate records total private length. Head suffix insertion
and tail prefix shifting preserve every full source/vector payload. -/
def mergeData : List RawOperator → Nat×List RawPair
  | [] => (0,[])
  | op::ops =>
    let tail := mergeData ops
    (op.1.length+tail.1,
      shiftPair op.1.length tail.1 (op.2.1,op.2.2) ::
        tail.2.map (shiftPair 0 op.1.length))

def bodyCode (vs : List Nat) : Nat :=
  vs.foldr (fun v tail => 8*Nat.pair (ContextInsertionCode.sourceCode 0 1 v) tail+5) 0

def chainCode (vs : List Nat) : Nat := 8*Nat.pair 0 (bodyCode vs)+6

/-- One literal final lambda; the actual assignment compiler returns every
field, including scalar. Invalid raw operators can fail assignment. -/
def compileCode (Γ : List Nat) (ops : List RawOperator) : Option (List Nat×Nat×List Nat) := do
  let ctx := contextCode Γ ops
  let src := chainCode ((mergeData ops).2.map Prod.fst)
  let v ← DefaultSourceAssignment.assignmentCode ctx src
  pure (ctx,src,v)
end LogicLineages.OrdinalComparison.Source.NumericUnaryChain
