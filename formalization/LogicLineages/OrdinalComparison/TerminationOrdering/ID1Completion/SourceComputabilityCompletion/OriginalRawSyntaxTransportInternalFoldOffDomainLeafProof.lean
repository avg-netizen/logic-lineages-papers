module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldOffDomainLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof (andLeft andRight)
open OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Neither malformed nil payloads nor unknown tags are silently decoded as
source syntax. Their only relevant property is the literal branch exclusion. -/
def NonStructural (tag : OTerm alpha) : Formula alpha :=
  (equal tag (numeral 1)).not ⊓ ((equal tag (numeral 4)).not ⊓
    ((equal tag (numeral 2)).not ⊓ ((equal tag (numeral 5)).not ⊓ (equal tag (numeral 7)).not)))

theorem nonStructuralArity (raw tag : OTerm alpha)
    (ht : Nonempty (Derivation positive Delta (graph1 rawTag tag raw)))
    (hn : Nonempty (Derivation positive Delta (NonStructural tag))) :
    Nonempty (Derivation positive Delta (graph1 (arityOf (.projection 0)) z raw)) := by
  let xs : Fin 1 → OTerm alpha := ![raw]
  have hl := unaryValue InternalUnpair.left (.projection 0) tag raw xs ht (projectionValue 0 xs)
  apply zeroBranchIntro _ _ _ z xs
    (sameReject _ _ tag (numeral 1) xs hl (constantValue 1 xs) (andLeft hn))
  apply zeroBranchIntro _ _ _ z xs
    (sameReject _ _ tag (numeral 4) xs hl (constantValue 4 xs) (andLeft (andRight hn)))
  apply zeroBranchIntro _ _ _ z xs
    (sameReject _ _ tag (numeral 2) xs hl (constantValue 2 xs) (andLeft (andRight (andRight hn))))
  apply zeroBranchIntro _ _ _ z xs
    (sameReject _ _ tag (numeral 5) xs hl (constantValue 5 xs) (andLeft (andRight (andRight (andRight hn)))))
  exact zeroBranchIntro _ _ _ z xs
    (sameReject _ _ tag (numeral 7) xs hl (constantValue 7 xs) (andRight (andRight (andRight (andRight hn)))))
    (constantValue 0 xs)

theorem unknownForward (mode : Mode) (raw out d k tag : OTerm alpha)
    (ht : Nonempty (Derivation positive Delta (graph1 rawTag tag raw)))
    (hz : Nonempty (Derivation positive Delta (equal tag z).not))
    (hn : Nonempty (Derivation positive Delta (NonStructural tag)))
    (ho : Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw))) :
    Nonempty (Derivation positive Delta (UnchangedLeafResult mode out raw)) :=
  unchangedForward mode raw out d k tag (nonStructuralArity raw tag ht hn) ht hz ho

theorem unknownBackward (mode : Mode) (raw out d k tag : OTerm alpha)
    (ht : Nonempty (Derivation positive Delta (graph1 rawTag tag raw)))
    (hz : Nonempty (Derivation positive Delta (equal tag z).not))
    (hn : Nonempty (Derivation positive Delta (NonStructural tag)))
    (ho : Nonempty (Derivation positive Delta (UnchangedLeafResult mode out raw))) :
    Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw)) :=
  unchangedBackward mode raw out d k tag (nonStructuralArity raw tag ht hn) ht hz ho

/-- This is deliberately every tag-six raw input, with no payload=0 premise. -/
theorem nilPayloadForward (mode : Mode) (raw out d k : OTerm alpha)
    (ht : Nonempty (Derivation positive Delta (graph1 rawTag (numeral 6) raw)))
    (ho : Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw))) :
    Nonempty (Derivation positive Delta (UnchangedLeafResult mode out raw)) :=
  unchangedForward mode raw out d k (numeral 6)
    (arityTag6 (.projection 0) ![raw]
      (unaryValue InternalUnpair.left (.projection 0) (numeral 6) raw ![raw] ht (projectionValue 0 ![raw])))
    ht (numeralNe 6 0 (by decide)) ho

theorem nilPayloadBackward (mode : Mode) (raw out d k : OTerm alpha)
    (ht : Nonempty (Derivation positive Delta (graph1 rawTag (numeral 6) raw)))
    (ho : Nonempty (Derivation positive Delta (UnchangedLeafResult mode out raw))) :
    Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw)) :=
  unchangedBackward mode raw out d k (numeral 6)
    (arityTag6 (.projection 0) ![raw]
      (unaryValue InternalUnpair.left (.projection 0) (numeral 6) raw ![raw] ht (projectionValue 0 ![raw])))
    ht (numeralNe 6 0 (by decide)) ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldOffDomainLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldOffDomainLeafProof
