module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnChildrenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnArgumentsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedAuxiliaryCoding NumberedMultisetNumeric
open OriginalHereditaryAgendaDefinitions OriginalHereditaryExpectedDefinitions OriginalHereditarySettledObserverDefinitions
open OriginalHereditaryExpectedReturnSupportProof OriginalHereditaryTypedJobDecorationProof
open OriginalHereditaryWorkBound OriginalHereditaryFiniteObserver
open OriginalRawSyntaxTransport (arityValue tagValue)
open OriginalHereditaryAnnotatedExpansion (annotationValue)

theorem termAtDepth (R : Program 2) {n : Nat} {arity : Fin n → Nat} (c : Nat)
 {Gamma : List Ty} (q : Packed (Fin n) arity Gamma) (depth : Nat)
 (h : OriginalHereditaryNativeBoundDefinitions.weight ⟨Gamma,q⟩ ≤ depth) :
 Expected arity R c (termJob q) (OriginalHereditaryReturn.scalar (family R depth) c q) := by
 have he := OriginalHereditaryFiniteStabilityProof.settled R n arity c ⟨Gamma,q⟩ depth h
 change OriginalHereditaryReturn.scalar (family R depth) c q = _ at he
 rw [he]
 exact expectedTerm R c q

theorem argumentsAtDepth (R : Program 2) {n : Nat} {arity : Fin n → Nat} (c : Nat)
 {Gamma types : List Ty} (args : AuxArguments (Fin n) arity Gamma types) (depth : Nat)
 (h : ∀ q ∈ argumentList args, OriginalHereditaryNativeBoundDefinitions.weight ⟨Gamma,q⟩ ≤ depth) :
 Expected arity R c (argumentJob args)
   (numbersNumber (OriginalRootObservation.argumentValues (family R depth) c args)) := by
 rw [OriginalHereditaryExpectedJointDepthProof.argumentsAtDepth R c args depth h]
 exact expectedArguments R c args

theorem argumentChildrenExpected (R : Program 2) {n c : Nat} {arity : Fin n → Nat} {Gamma types : List Ty}
 (args : AuxArguments (Fin n) arity Gamma types) (depth : Nat)
 (h : ∀ q ∈ argumentList args, OriginalHereditaryNativeBoundDefinitions.weight ⟨Gamma,q⟩ ≤ depth) :
 List.Forall₂ (Expected arity R c)
   (decorate c (argumentJob args) 0 (children Gamma (argumentsCode args)))
   (OriginalHereditaryReturnStep.argumentChildren (family R depth) c args) := by
 cases args with
 | nil => exact .nil
 | cons q rest =>
   have hq := termAtDepth R c ⟨_,q⟩ depth (h _ (List.mem_cons_self))
   have hr := argumentsAtDepth R c rest depth (fun q hq => h q (List.mem_cons_of_mem _ hq))
   have hh := List.Forall₂.cons hq (List.Forall₂.cons hr List.Forall₂.nil)
   simpa [termJob,argumentJob,argumentsCode,children,decorate,childAnnotation,annotationValue,arityValue,tagValue,
     codeNumber,Nat.unpair_pair,OriginalHereditaryReturnStep.argumentChildren] using hh

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnArgumentsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnArgumentsProof
