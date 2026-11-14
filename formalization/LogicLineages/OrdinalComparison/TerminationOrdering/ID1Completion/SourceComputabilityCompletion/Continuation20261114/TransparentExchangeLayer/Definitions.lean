module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeAnswerSlots.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def validValue (n : Nat) (v : List.Vector Nat 3) : Nat :=
  match Encodable.decode (α := ExchangeNumericSuppliers.Node n) (v.get 0),
      Encodable.decode (α := ExchangeNumericSuppliers.Window n) (v.get 2) with
  | some _, some _ => 1
  | _, _ => 0
/-- Original all-input field specification. Unused malformed fields default zero;
the optional layer guard must still reject before field interpretation matters. -/
def fieldValue (n : Nat) (arity : Fin n → Nat) (i : Fin 19) (v : List.Vector Nat 3) : Nat :=
  match Encodable.decode (α := ExchangeNumericSuppliers.Node n) (v.get 0),
      Encodable.decode (α := ExchangeNumericSuppliers.Window n) (v.get 2) with
  | some p, some window =>
    (ExchangeLayer.input n arity (window,NumberedExchangeCodeFieldsProof.fields p.1,
      NumberedExchangeCodeFieldsProof.fields p.2,
      ((NumberedMultisetNumeric.decodeNumbers (v.get 1)).getD []).map (fun value => value == 1))).get i
  | _, _ => 0
/-- Recursion-answer slots are ACTUAL lookup ASTs, never supplied opaquely. -/
def fields (U : Fin 19 → Program 3) (i : Fin 19) : Program 3 :=
  if i = 14 then ExchangeAnswerSlots.answer 0 else
  if i = 15 then ExchangeAnswerSlots.answer 3 else U i
def body (U : Fin 19 → Program 3) : Program 3 := .composition ExchangeLayer.layer (fields U)
/-- The original optional layer: false=Some0=1, true=Some1=2.
Invalid node/window has the explicit Some0 extension, not None=0. -/
def optional (U : Fin 19 → Program 3) (V : Program 3) : Program 3 :=
  InternalAcceptance.branch V (InternalLessThan.constantOne 3)
    (.composition .succ (fun _ : Fin 1 => body U))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer
