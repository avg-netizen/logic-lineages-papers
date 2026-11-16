module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardObservationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261115 OriginalRawSyntaxTransport
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

/-- Eliminate the actual total field observations before using original guard
constructor inversion. No raw encoding or recursively supplied validity premise. -/
theorem cases (n : Nat) (raw : OTerm alpha) (psi : Formula alpha)
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (tag payload first second head : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (raw.relabel j) tag payload)) →
      Nonempty (Derivation body Theta (graph1 (firstOf (.projection 0)) first (raw.relabel j))) →
      Nonempty (Derivation body Theta (graph1 (secondOf (.projection 0)) second (raw.relabel j))) →
      Nonempty (Derivation body Theta (graph1 (OriginalCodeValidityGuard.FieldProof.headOf (.projection 0)) head (raw.relabel j))) →
      Nonempty (Derivation body Theta (OriginalCodeValidityConstructors.Targets.allowed n tag payload first second head)) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  apply OriginalCodeValidityGuard.FieldProof.fieldCases raw psi
  intro beta j Theta tag payload first second head hj hp hf hs hh
  have hvj := renameInto hv j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hvj
  have ha := (OriginalCodeValidityConstructors.Proof.guardConstructors n body beta Theta
    (raw.relabel j) tag payload first second head hp hf hs hh).mp hvj
  exact next beta j Theta tag payload first second head hj hp hf hs hh ha
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardObservationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardObservationProof
