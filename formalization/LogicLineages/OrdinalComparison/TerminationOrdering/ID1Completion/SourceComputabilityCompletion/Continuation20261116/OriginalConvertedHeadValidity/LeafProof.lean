module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.ClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.LeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.LeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open InternalQuotientComparisonProof (orLeft orRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115 OriginalEncodedHeadConversion
open ClosureProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem basic (n : Nat) (raw : OTerm alpha) (tag : Fin 2)
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing raw (numeral tag.val) z))) :
    Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) raw)) := by
  apply OriginalHeadDecoderValidity.BackwardProof.backward n raw (numeral tag.val) z hp
  fin_cases tag
  · exact ⟨orLeft (Derivation.conjunctionIntroduction (orLeft (refl _)) (refl _))⟩
  · exact ⟨orLeft (Derivation.conjunctionIntroduction (orRight (refl _)) (refl _))⟩

theorem zero (n : Nat) {k : Nat} : ValidOutput n (constant k 0) := by
  intro body alpha Delta xs out h
  have hv := basic (body := body) (Delta := Delta) n (z : OTerm alpha) 0 InternalApplicationValidityStackAppendTransitionProof.pairZero
  have he := valueUnique (constant k 0) z out xs (constantValue 0 xs) h
  exact headTransport (OriginalHeadDecoderValidity.check n) (numeral 1) z out Fin.elim0 he hv

theorem payload (n : Nat) (tag : Fin 3) : ValidOutput n (payloadHead (tag.val+2)) := by
  intro body alpha Delta xs out h
  have hp := binaryRecover InternalPairing.pairing (constant 1 (tag.val+2)) (.projection 0)
    out (numeral (tag.val+2)) (xs 0) xs h (constantValue (tag.val+2) xs) (projectionValue 0 xs)
  apply OriginalHeadDecoderValidity.BackwardProof.backward n out (numeral (tag.val+2)) (xs 0) hp
  fin_cases tag
  · exact ⟨orRight (orLeft (refl _))⟩
  · exact ⟨orRight (orRight (orLeft (refl _)))⟩
  · exact ⟨orRight (orRight (orRight (orLeft (refl _))))⟩

theorem one (n : Nat) : ValidOutput n
    (pairOf (constant 1 1) (constant 1 0)) := by
  intro body alpha Delta xs out h
  exact basic n out 1 (binaryRecover InternalPairing.pairing (constant 1 1) (constant 1 0)
    out (numeral 1) z xs h (constantValue 1 xs) (constantValue 0 xs))

theorem boolean (n : Nat) : ValidOutput n booleanHead :=
  branch n _ _ _ (zero n) (one n)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.LeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.LeafProof
