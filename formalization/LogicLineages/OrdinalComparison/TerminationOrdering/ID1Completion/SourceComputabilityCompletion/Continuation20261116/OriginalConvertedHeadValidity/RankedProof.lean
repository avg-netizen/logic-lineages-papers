module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.LeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.RankedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof InternalAcceptanceBranchProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open InternalQuotientComparisonProof (orLeft orRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115 OriginalEncodedHeadConversion ClosureProof
attribute [local irreducible] programGraph

theorem ranked (n : Nat) : ValidOutput n (rankedHead n) := by
  intro body alpha Delta xs out h
  let C := InternalLessThan.strictLess (xs 0) (numeral n)
  let test : Program 1 := .composition InternalLessThan.ltTest ![.projection 0,constant 1 n]
  apply formulaCases C
  · have hl : Nonempty (Derivation body (C :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ht := binaryValue InternalLessThan.ltTest (.projection 0) (constant 1 n)
      (suc z) (xs 0) (numeral n) xs (InternalLessThanSupportProof.acceptOfLess _ _ hl)
      (projectionValue 0 xs) (constantValue n xs)
    have hb := successorBranchElim test (constant 1 0) (payloadHead 5) out z xs ht (withHyp h C)
    have hp := binaryRecover InternalPairing.pairing (constant 1 5) (.projection 0)
      out (numeral 5) (xs 0) xs hb (constantValue 5 xs) (projectionValue 0 xs)
    apply OriginalHeadDecoderValidity.BackwardProof.backward n out (numeral 5) (xs 0) hp
    exact ⟨orRight (orRight (orRight (orRight (Derivation.conjunctionIntroduction (refl _) (Classical.choice hl)))))⟩
  · have hl : Nonempty (Derivation body (C.not :: Delta) C.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ht := binaryValue InternalLessThan.ltTest (.projection 0) (constant 1 n)
      z (xs 0) (numeral n) xs (InternalLessThanSupportProof.rejectOfNotLess _ _ hl)
      (projectionValue 0 xs) (constantValue n xs)
    exact LeafProof.zero n body alpha _ xs out
      (zeroBranchElim test (constant 1 0) (payloadHead 5) out xs ht (withHyp h C.not))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.RankedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.RankedProof
