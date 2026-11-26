module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceAgreementProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceUnaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open OriginalTypedArgumentObservationsCongruence OriginalTypedArgumentObservationsCongruenceSyntaxProof
open OriginalTypedArgumentObservationsAccumulatorQueryProof OriginalTypedArgumentObservationsCongruenceAgreementProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem unaryForward (P : Program 1) (F G : Program 2) (parameter input out : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (Agreement F G parameter)))
 (ho : Nonempty (Derivation body Delta (graph2 (.composition P (fun _ : Fin 1 => F)) out input parameter))) :
 Nonempty (Derivation body Delta (graph2 (.composition P (fun _ : Fin 1 => G)) out input parameter)) := by
 apply binaryCases F input parameter _
 intro beta j Theta value hj hv
 rw [graph2Rename]
 have hf' := renameInto hf j Theta hj
 have ho' := renameInto ho j Theta hj
 rw [agreementRename] at hf'
 rw [graph2Rename] at ho'
 let xs : Fin 2 → OTerm beta := Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
 have hp := unaryRecover P F (out.relabel j) value xs ho' hv
 exact unaryValue P G (out.relabel j) value xs hp
   (agreementForward F G (parameter.relabel j) (input.relabel j) value hf' hv)

theorem unaryAgreement (P : Program 1) (F G : Program 2) (parameter : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (Agreement F G parameter))) :
 Nonempty (Derivation body Delta (Agreement (.composition P (fun _ : Fin 1 => F)) (.composition P (fun _ : Fin 1 => G)) parameter)) := by
 apply agreementIntro _ _ parameter
 intro beta j Theta input left right hj hl hr
 have hf' := renameInto hf j Theta hj
 rw [agreementRename] at hf'
 have hleft := unaryForward P F G (parameter.relabel j) input left hf' hl
 simpa only [equalEqn] using valueUnique (.composition P (fun _ : Fin 1 => G)) left right
   (Fin.cons input (Fin.cons (parameter.relabel j) Fin.elim0)) hleft hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceUnaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceUnaryProof
