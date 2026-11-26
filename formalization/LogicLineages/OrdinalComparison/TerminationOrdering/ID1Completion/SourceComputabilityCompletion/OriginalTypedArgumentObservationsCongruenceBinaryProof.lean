module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceAgreementProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceBinaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalTypedArgumentObservationsCongruence OriginalTypedArgumentObservationsCongruenceSyntaxProof
open OriginalTypedArgumentObservationsAccumulatorQueryProof OriginalTypedArgumentObservationsCongruenceAgreementProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem binaryForward (P F G U V : Program 2) (parameter input out : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (Agreement F G parameter)))
 (hu : Nonempty (Derivation body Delta (Agreement U V parameter)))
 (ho : Nonempty (Derivation body Delta (graph2 (.composition P ![F,U]) out input parameter))) :
 Nonempty (Derivation body Delta (graph2 (.composition P ![G,V]) out input parameter)) := by
 apply binaryCases F input parameter _
 intro beta j Theta first hj hfirst
 rw [graph2Rename]
 have hf' := renameInto hf j Theta hj
 have hu' := renameInto hu j Theta hj
 have ho' := renameInto ho j Theta hj
 rw [agreementRename] at hf' hu'
 rw [graph2Rename] at ho'
 apply binaryCases U (input.relabel j) (parameter.relabel j) _
 intro gamma k Xi second hk hsecond
 rw [graph2Rename]
 have hf'' := renameInto hf' k Xi hk
 have hu'' := renameInto hu' k Xi hk
 have ho'' := renameInto ho' k Xi hk
 have hfirst' := renameInto hfirst k Xi hk
 rw [agreementRename] at hf'' hu''
 rw [graph2Rename] at ho'' hfirst'
 let xs : Fin 2 → OTerm gamma := Fin.cons ((input.relabel j).relabel k)
   (Fin.cons ((parameter.relabel j).relabel k) Fin.elim0)
 have hp := binaryRecover P F U ((out.relabel j).relabel k) (first.relabel k) second xs ho'' hfirst' hsecond
 have hg := agreementForward F G ((parameter.relabel j).relabel k) ((input.relabel j).relabel k) (first.relabel k) hf'' hfirst'
 have hv := agreementForward U V ((parameter.relabel j).relabel k) ((input.relabel j).relabel k) second hu'' hsecond
 exact binaryValue P G V ((out.relabel j).relabel k) (first.relabel k) second xs hp hg hv

theorem binaryAgreement (P F G U V : Program 2) (parameter : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (Agreement F G parameter)))
 (hu : Nonempty (Derivation body Delta (Agreement U V parameter))) :
 Nonempty (Derivation body Delta (Agreement (.composition P ![F,U]) (.composition P ![G,V]) parameter)) := by
 apply agreementIntro _ _ parameter
 intro beta j Theta input left right hj hl hr
 have hf' := renameInto hf j Theta hj
 have hu' := renameInto hu j Theta hj
 rw [agreementRename] at hf' hu'
 have hleft := binaryForward P F G U V (parameter.relabel j) input left hf' hu' hl
 simpa only [equalEqn] using valueUnique (.composition P ![G,V]) left right
   (Fin.cons input (Fin.cons (parameter.relabel j) Fin.elim0)) hleft hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceBinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceBinaryProof
