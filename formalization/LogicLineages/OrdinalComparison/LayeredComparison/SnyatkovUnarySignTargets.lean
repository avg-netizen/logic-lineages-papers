module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnarySignDefinitions
public import Mathlib.Computability.Primrec.List
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnarySign.Targets

/-- Actual sign of every signed-Phi+linear normal form at EVERY input above
the displayed computed threshold. Also derives genuine original signed-shift
domains from ALL original occurrences, including zeros and cancellation. No
leading-sign/evaluation/tail-growth premise or oracle is supplied. -/
def OriginalDomainAndTailSign : Prop := ∀ E : Expression,
  domainBound E ≤ threshold E ∧
  ∀ n : Nat, threshold E ≤ n →
    (∀ a ∈ E.1, 0 ≤ (n : Int) + a.2) ∧ Int.sign (value E n) = tailSign E

/-- Exact numerical source evaluation and the actual least domain/computed
tail threshold/tail sign are primitive recursive under standard list/Int codes. -/
def ActualPrimitiveRecursion : Prop :=
  Primrec₂ value ∧ Primrec domainBound ∧ Primrec threshold ∧ Primrec tailSign

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnarySign.Targets
