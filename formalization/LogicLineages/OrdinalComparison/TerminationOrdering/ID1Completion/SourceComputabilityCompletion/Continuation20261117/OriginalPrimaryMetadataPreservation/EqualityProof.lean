module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.SyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.EqualityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open SyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof (refl)

theorem pairFields (p q a b x y : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p a b)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing q x y)))
    (he : Nonempty (Derivation body Delta (eqn p q))) :
    Nonempty (Derivation body Delta (eqn a x ⊓ eqn b y)) := by
  have hl := headTransport InternalUnpair.left a p q Fin.elim0 he (pairLeft p a b hp)
  have hr := headTransport InternalUnpair.right b p q Fin.elim0 he (pairRight p a b hp)
  obtain ⟨ha⟩ := valueUnique InternalUnpair.left a x (Fin.cons q Fin.elim0) hl (pairLeft q x y hq)
  obtain ⟨hb⟩ := valueUnique InternalUnpair.right b y (Fin.cons q Fin.elim0) hr (pairRight q x y hq)
  exact ⟨Derivation.conjunctionIntroduction ha hb⟩

theorem acceptedFields (n : Nat) (arity : Fin n → Nat)
    (leftType rightType leftRaw rightRaw rootTypeRef boundsRef : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (eqn leftType rightType)))
    (hr : Nonempty (Derivation body Delta (eqn leftRaw rightRaw)))
    (ha : Nonempty (Derivation body Delta (accepted n arity leftType leftRaw rootTypeRef boundsRef))) :
    Nonempty (Derivation body Delta (accepted n arity rightType rightRaw rootTypeRef boundsRef)) := by
  have htyp := andLeft ha
  have hraw := andRight ha
  obtain ⟨htyp⟩ := htyp
  obtain ⟨ht⟩ := ht
  have hb := headTransport (OriginalCodeBoundsRecursion.bounds n) boundsRef leftRaw rightRaw Fin.elim0 hr hraw
  exact andIntro ⟨InternalTagArithmeticSupportProof.trans htyp ht⟩ hb

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.EqualityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.EqualityProof
