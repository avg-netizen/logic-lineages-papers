module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseConsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseAccumulatorCompatibilityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseConsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding OTerm
open InternalTagArithmeticSupportProof
open OriginalTypedArgumentObservationsReverseInternalAccumulatorDefinitions (accumulated)
open OriginalTypedArgumentObservations (reverse)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem toOriginal (raw out : OTerm alpha)
 (h : Nonempty (Derivation body Delta (graph2 accumulated out raw z))) :
 Nonempty (Derivation body Delta (graph1 reverse out raw)) := by
 obtain ⟨he⟩ := OriginalTypedArgumentObservationsReverseInternalAccumulatorZeroProof.zeroCorrespondence body alpha raw out
 exact closedApply ⟨Derivation.conjunctionLeft he⟩ h

theorem zero : Nonempty (Derivation body Delta (graph1 reverse (z : OTerm alpha) z)) :=
 toOriginal z z (OriginalTypedArgumentObservationsReverseInternalAccumulatorConsProof.zero z)

theorem atAccumulator (raw head tail singleton mapped out actual : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleton head z)))
 (hm : Nonempty (Derivation body Delta (graph1 reverse mapped tail)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out mapped singleton)))
 (hv : Nonempty (Derivation body Delta (graph2 accumulated actual tail singleton))) :
 Nonempty (Derivation body Delta (graph1 reverse out raw)) := by
 have htail := OriginalTypedArgumentObservationsReverseInternalProof.fromOriginal tail mapped hm
 have hp := OriginalReverseAccumulatorCompatibilityProof.actualCompatibility body alpha Delta
   tail z singleton singleton mapped actual
   (InternalApplicationValidityStackAppendListProof.appendZeroValue singleton) htail hv
 have he := valueUnique InternalApplicationValidityStackAppend.append actual out ![mapped,singleton] hp ha
 have hr := OriginalTypedArgumentObservationsReverseInternalAccumulatorConsProof.consValue raw head tail z singleton actual hc hs hv
 exact toOriginal raw out (outputTransport accumulated actual out ![raw,z] he hr)

theorem actualCons : OriginalReverseConsTargets.ActualCons := by
 intro body alpha Delta raw head tail singleton mapped out hc hs hm ha
 apply programCases accumulated (Fin.cons tail (Fin.cons singleton Fin.elim0)) _
 intro beta rho Theta actual hrho hv
 simp only [consTermRename,emptyRename] at hv
 simp only [graph1Rename]
 have hc' := renameInto hc rho Theta hrho
 have hs' := renameInto hs rho Theta hrho
 have hm' := renameInto hm rho Theta hrho
 have ha' := renameInto ha rho Theta hrho
 simp only [graph2Rename,zRelabel] at hc' hs' ha'
 rw [graph1Rename] at hm'
 exact atAccumulator (raw.relabel rho) (head.relabel rho) (tail.relabel rho) (singleton.relabel rho)
   (mapped.relabel rho) (out.relabel rho) actual hc' hs' hm' ha' hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseConsProof
