module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedJointDepthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySettledObserverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobChildrenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnChildrenProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedAuxiliaryCoding NumberedMultisetNumeric
open OriginalHereditaryAgendaDefinitions OriginalHereditaryExpectedDefinitions OriginalHereditarySettledObserverDefinitions
open OriginalHereditaryExpectedReturnSupportProof
open OriginalHereditaryTypedJobDecorationProof OriginalHereditaryWorkBound
open OriginalHereditaryFiniteObserver
open OriginalRawSyntaxTransport (arityValue tagValue)
open OriginalHereditaryAnnotatedExpansion (annotationValue)

theorem expectedTermChild (R : Program 2) {n : Nat} {arity : Fin n → Nat} (c : Nat)
 (s : OriginalHereditaryNativeBoundDefinitions.State (Fin n) arity) {Gamma : List Ty}
 (q : Packed (Fin n) arity Gamma)
 (h : OriginalHereditaryNativeBoundDefinitions.Child s ⟨Gamma,q⟩) :
 Expected arity R c (termJob q)
   (OriginalHereditaryReturn.scalar (family R (OriginalHereditaryNativeBoundDefinitions.weight s)) c q) := by
 have he := OriginalHereditarySettledObserverProof.stepNormalization R n arity c s ⟨Gamma,q⟩
   (OriginalHereditaryNativeBoundDefinitions.Step.child h)
 change OriginalHereditaryReturn.scalar (family R (OriginalHereditaryNativeBoundDefinitions.weight s)) c q = _ at he
 rw [he]
 exact expectedTerm R c q

theorem expectedArgumentsChildren (R : Program 2) {n : Nat} {arity : Fin n → Nat} (c : Nat)
 (s : OriginalHereditaryNativeBoundDefinitions.State (Fin n) arity) {Gamma types : List Ty}
 (args : AuxArguments (Fin n) arity Gamma types)
 (h : ∀ q ∈ argumentList args, OriginalHereditaryNativeBoundDefinitions.Child s ⟨Gamma,q⟩) :
 Expected arity R c (argumentJob args)
   (numbersNumber (OriginalRootObservation.argumentValues
     (family R (OriginalHereditaryNativeBoundDefinitions.weight s)) c args)) := by
 rw [OriginalHereditaryExpectedJointDepthProof.argumentsAtDepth R c args _ (fun q hq =>
   Nat.le_of_lt (OriginalHereditaryNativeBoundProof.stepWeight
     (OriginalHereditaryNativeBoundDefinitions.Step.child (h q hq))))]
 exact expectedArguments R c args

theorem termChildrenExpected (R : Program 2) {n c : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
 (q : Packed (Fin n) arity Gamma) :
 List.Forall₂ (Expected arity R c)
   (decorate c (termJob q) 0 (children Gamma (termCode q.2)))
   (OriginalHereditaryReturnStep.termChildren
     (family R (OriginalHereditaryNativeBoundDefinitions.weight ⟨Gamma,q⟩)) c q) := by
 obtain ⟨tau,q⟩ := q
 cases q with
 | var v => exact .nil
 | bottom t => exact .nil
 | @lam Gamma d t body =>
   have hh := List.Forall₂.cons (expectedTermChild R c _ ⟨t,body⟩ (.lam body)) List.Forall₂.nil
   simpa [termJob,termCode,children,decorate,childAnnotation,annotationValue,arityValue,tagValue,
     codeNumber,typeNumber,Nat.unpair_pair,OriginalHereditaryReturnStep.termChildren] using hh
 | @app Gamma d t fn arg =>
   have hh := List.Forall₂.cons (expectedTermChild R c _ ⟨_,fn⟩ (.appFunction fn arg))
     (List.Forall₂.cons (expectedTermChild R c _ ⟨_,arg⟩ (.appArgument fn arg)) List.Forall₂.nil)
   simpa [termJob,termCode,children,decorate,childAnnotation,annotationValue,arityValue,tagValue,
     codeNumber,typeNumber,Nat.unpair_pair,OriginalHereditaryReturnStep.termChildren] using hh
 | ordinary head args =>
   have hh := List.Forall₂.cons (expectedArgumentsChildren R c _ args
     (fun q hq => .ordinary head args q hq)) List.Forall₂.nil
   simpa [termJob,argumentJob,termCode,children,decorate,childAnnotation,annotationValue,arityValue,tagValue,
     codeNumber,Nat.unpair_pair,OriginalHereditaryReturnStep.termChildren] using hh
 | numbered k head tau args extraTypes extras =>
   have hh := List.Forall₂.cons (expectedArgumentsChildren R c _ args
     (fun q hq => .numberedBase k head tau args extraTypes extras q hq))
     (List.Forall₂.cons (expectedArgumentsChildren R c _ extras
       (fun q hq => .numberedExtra k head tau args extraTypes extras q hq)) List.Forall₂.nil)
   simpa [termJob,argumentJob,termCode,children,decorate,childAnnotation,annotationValue,arityValue,tagValue,
     codeNumber,Nat.unpair_pair,OriginalHereditaryReturnStep.termChildren] using hh
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnChildrenProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnChildrenProof
