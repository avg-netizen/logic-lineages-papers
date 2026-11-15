module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBooleanRange.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotientDecoderProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- Explicit finite enumeration, no choice of a finite support or decoder oracle. -/
def vectors {alpha : Type} (values : List alpha) : (n : Nat) → List (Fin n → alpha)
  | 0 => [Fin.elim0]
  | n+1 => values.flatMap (fun a => (vectors values n).map (Fin.cons a))
/-- Original finite Boolean tables, with the original finPi Encodable instance. -/
def tables (n : Nat) : List (Fin n → Fin n → Bool) :=
  vectors (vectors [false,true] n) n
def tableCodes (n : Nat) : List Nat := (tables n).map Encodable.encode
def tableListCode (n : Nat) : Nat := NumberedMultisetNumeric.numbersNumber (tableCodes n)
/-- Literal finite membership test using the checked raw-list membership AST. -/
def tableGuard (n : Nat) : Program 1 :=
  .composition contains ![OriginalRawSyntaxTransport.constant 1 (tableListCode n),.projection 0]
/-- Actual Context product is Window × (Fin n → Fin n → Bool), not finArrow. -/
def contextGuard (n : Nat) : Program 1 :=
  InternalAcceptance.conjunction
    (.composition (OriginalDecodedWindowValidity.window n) (fun _ : Fin 1 => InternalUnpair.left))
    (.composition (tableGuard n) (fun _ : Fin 1 => InternalUnpair.right))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity
