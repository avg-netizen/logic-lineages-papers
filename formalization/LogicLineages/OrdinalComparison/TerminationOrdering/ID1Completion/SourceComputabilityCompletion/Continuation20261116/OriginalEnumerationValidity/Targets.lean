module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261115
/-- Every member of the actual full enumeration satisfies the original code
syntax guard. Node is the original pair(variableBound,fuel), but is quantified
as an arbitrary raw term: no supplied pair witness or encoded-image restriction.
The parameter remains the actual nested pair(types,heads,labels,tupleBound).
Validity of prior/opened lists is an induction duty, never an endpoint premise. -/
def InternalEnumerationValidity : Prop := ∀ (n : Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (node param out raw : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph2 (OriginalEnumerationRecursion.enumeration n) out node param)) →
  Nonempty (Derivation body Delta
    (graph2 contains (numeral 1) out raw)) →
  Nonempty (Derivation body Delta
    (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.Targets
