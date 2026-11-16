module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardChoiceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261115 OriginalRawSyntaxTransport
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (eqn)

theorem orConclusion {A B C : Formula alpha}
    (ha : Nonempty (Derivation body Delta (A.imp C)))
    (hb : Nonempty (Derivation body Delta (B.imp C))) :
    Nonempty (Derivation body Delta ((A ⊔ B).imp C)) := by
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  exact InternalBetaTotalityProof.disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
    (Classical.choice (withHyp ha (A ⊔ B))) (Classical.choice (withHyp hb (A ⊔ B)))

theorem andFirst {A B C : Formula alpha}
    (ha : Nonempty (Derivation body Delta (A.imp C))) :
    Nonempty (Derivation body Delta ((A ⊓ B).imp C)) := by
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  exact Derivation.implicationElimination (Classical.choice (withHyp ha (A ⊓ B)))
    (Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self))

/-- Exhaust the original guard's exact tag alternatives, retaining the nil
payload-zero side condition. All eight cases are supplied as internal implications. -/
theorem eliminate (n : Nat) (tag payload first second head : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (OriginalCodeValidityConstructors.Targets.allowed n tag payload first second head)))
    (h0 : Nonempty (Derivation body Delta ((eqn tag (numeral 0)).imp psi)))
    (h1 : Nonempty (Derivation body Delta ((eqn tag (numeral 1)).imp psi)))
    (h2 : Nonempty (Derivation body Delta ((eqn tag (numeral 2)).imp psi)))
    (h3 : Nonempty (Derivation body Delta ((eqn tag (numeral 3)).imp psi)))
    (h4 : Nonempty (Derivation body Delta ((eqn tag (numeral 4)).imp psi)))
    (h5 : Nonempty (Derivation body Delta ((eqn tag (numeral 5)).imp psi)))
    (h6 : Nonempty (Derivation body Delta ((eqn tag (numeral 6) ⊓ eqn payload (numeral 0)).imp psi)))
    (h7 : Nonempty (Derivation body Delta ((eqn tag (numeral 7)).imp psi))) :
    Nonempty (Derivation body Delta psi) := by
  have hd : Nonempty (Derivation body Delta
      ((OriginalCodeValidityConstructors.Targets.allowed n tag payload first second head).imp psi)) := orConclusion (orConclusion h0 h3)
    (orConclusion (andFirst h1)
      (orConclusion (andFirst (orConclusion h2 h7))
        (orConclusion (andFirst h4) (orConclusion (andFirst h5) h6))))
  exact ⟨Derivation.implicationElimination (Classical.choice hd) (Classical.choice h)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardChoiceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardChoiceProof
