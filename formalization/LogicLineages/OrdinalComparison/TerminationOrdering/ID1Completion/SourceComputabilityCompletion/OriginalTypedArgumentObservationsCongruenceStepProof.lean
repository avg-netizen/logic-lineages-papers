module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceAdvanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open OriginalTypedArgumentObservationsCongruence OriginalTypedArgumentObservationsCongruenceSyntaxProof
open OriginalTypedArgumentObservationsAccumulatorQueryProof OriginalTypedArgumentObservationsCongruenceAgreementProof
open OriginalTypedArgumentObservationsCongruenceAdvanceProof OriginalTypedArgumentObservations
open OriginalTypedDecoderInternalBranchProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] walkStep advance

theorem stepForward (R S : Program 2) (parameter input out : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Agreement R S parameter)))
 (ho : Nonempty (Derivation body Delta (graph2 (walkStep R) out input parameter))) :
 Nonempty (Derivation body Delta (graph2 (walkStep S) out input parameter)) := by
 apply binaryCases (leftOf remaining) input parameter _
 intro beta j Theta tag hj ht
 rw [graph2Rename]
 have ha' := renameInto ha j Theta hj
 have ho' := renameInto ho j Theta hj
 rw [agreementRename] at ha'
 rw [graph2Rename] at ho'
 let xs : Fin 2 → OTerm beta := Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
 have hn := constantValue (body := body) (Delta := Theta) 7 xs
 let E := equal tag (numeral 7)
 apply formulaCases E _
 · have he : Nonempty (Derivation body (E :: Theta) E) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hr := sameYesElim (leftOf remaining) (OriginalRawSyntaxTransport.constant 2 7)
     (advance R) (.projection 0) (out.relabel j) tag (numeral 7) xs
     (withHyp ht E) (withHyp hn E) he (by simpa only [walkStep] using withHyp ho' E)
   have hs := agreementForward (advance R) (advance S) (parameter.relabel j) (input.relabel j) (out.relabel j)
     (advanceAgreement R S (parameter.relabel j) (withHyp ha' E)) hr
   simpa only [walkStep] using sameYesIntro (leftOf remaining) (OriginalRawSyntaxTransport.constant 2 7)
     (advance S) (.projection 0) (out.relabel j) tag (numeral 7) xs (withHyp ht E) (withHyp hn E) he hs
 · have he : Nonempty (Derivation body (E.not :: Theta) E.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hr := sameNoElim (leftOf remaining) (OriginalRawSyntaxTransport.constant 2 7)
     (advance R) (.projection 0) (out.relabel j) tag (numeral 7) xs
     (withHyp ht E.not) (withHyp hn E.not) he (by simpa only [walkStep] using withHyp ho' E.not)
   simpa only [walkStep] using sameNoIntro (leftOf remaining) (OriginalRawSyntaxTransport.constant 2 7)
     (advance S) (.projection 0) (out.relabel j) tag (numeral 7) xs
     (withHyp ht E.not) (withHyp hn E.not) he hr

theorem stepAgreement (R S : Program 2) (parameter : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Agreement R S parameter))) :
 Nonempty (Derivation body Delta (Agreement (walkStep R) (walkStep S) parameter)) := by
 apply agreementIntro _ _ parameter
 intro beta j Theta input left right hj hl hr
 have ha' := renameInto ha j Theta hj
 rw [agreementRename] at ha'
 have hleft := stepForward R S (parameter.relabel j) input left ha' hl
 simpa only [equalEqn] using valueUnique (walkStep S) left right
   (Fin.cons input (Fin.cons (parameter.relabel j) Fin.elim0)) hleft hr

theorem actualStepCongruence : OriginalTypedArgumentObservationsCongruenceTargets.StepCongruence := by
 intro R S body alpha Delta parameter
 obtain ⟨h⟩ := stepAgreement R S parameter (body := body) (Delta := Agreement R S parameter :: Delta)
   ⟨Derivation.hypothesis List.mem_cons_self⟩
 exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceStepProof
