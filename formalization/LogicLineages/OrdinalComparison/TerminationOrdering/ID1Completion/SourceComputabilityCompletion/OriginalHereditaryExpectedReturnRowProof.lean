module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionDeletionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySettledObserverProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnRowProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedAuxiliaryCoding NumberedMultisetNumeric
open OriginalHereditaryAgendaDefinitions OriginalHereditaryExpectedDefinitions OriginalHereditarySettledObserverDefinitions
open OriginalHereditaryWorkBound OriginalRawSyntaxTransport
open OriginalHereditaryExpansionDeletionProof

def rawValue (Q : Program 2) {n : Nat} (tau : Ty) (c : Nat) (s : State (Fin n)) : Nat :=
 evaluate Q (List.Vector.ofFn ![Nat.pair (typeNumber tau) (codeNumber s.code),Nat.pair c (Encodable.encode s.context)])

theorem observationAt (Q : Program 2) {n : Nat} (tau : Ty) (c : Nat) (code : Code (Fin n))
 (binders tail : List Ty) (sigma : Ty) :
 evaluate (OriginalHereditaryDeletionRows.observation Q)
   (List.Vector.ofFn ![binders.length,Nat.pair (typeNumber tau) (codeNumber code),
     Nat.pair c (Encodable.encode (binders ++ sigma::tail))]) =
 rawValue Q tau c ⟨binders ++ tail,eraseCode sigma binders.length code⟩ := by
 rw [OriginalHereditaryDeletionRowsNativeProof.observationPrefix]
 unfold OriginalClassContextPrefixNative.erasedPacked
 rw [OriginalRawObjectTransportEvaluationProof.erasePackedEvaluation]
 simp only [Nat.unpair_pair]
 rw [OriginalRawSyntaxTransportCodeProof.actualRawSyntaxCodeCalibration.2.1 n binders.length sigma code]
 rfl

theorem observationMap (Q : Program 2) {n : Nat} (tau : Ty) (c : Nat) (code : Code (Fin n))
 (binders tail : List Ty) :
 (List.range tail.length).map (fun k =>
   evaluate (OriginalHereditaryDeletionRows.observation Q)
     (List.Vector.ofFn ![binders.length+k,Nat.pair (typeNumber tau) (codeNumber code),
       Nat.pair c (Encodable.encode (binders ++ tail))])) =
 (deletionsFrom code binders tail).map (rawValue Q tau c) := by
 apply prefixMap
   (fun k Gamma => evaluate (OriginalHereditaryDeletionRows.observation Q)
     (List.Vector.ofFn ![k,Nat.pair (typeNumber tau) (codeNumber code),Nat.pair c (Encodable.encode Gamma)]))
   (fun bs ts => (deletionsFrom code bs ts).map (rawValue Q tau c))
 · intro bs; rfl
 · intro bs sigma ts
   rw [observationAt]
   rfl

theorem rowsAt (Q : Program 2) {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
 (c : Nat) (q : Packed (Fin n) arity Gamma) :
 OriginalHereditaryFiniteStability.value (OriginalHereditaryDeletionRows.rows Q) c ⟨Gamma,q⟩ =
 numbersNumber ((deletionsFrom (termCode q.2) [] Gamma).map (rawValue Q q.1 c)) := by
 unfold OriginalHereditaryFiniteStability.value
 rw [OriginalHereditaryDeletionRowsBoundProof.nativeRows]
 simp only [Nat.unpair_pair]
 rw [← OriginalTypedDecoderReconstructionLocalProof.contextNumber,
   OriginalContextInsertionCalibrationProof.lengthContext]
 unfold OriginalHereditaryDeletionRows.values
 have hm := observationMap Q q.1 c (termCode q.2) [] Gamma
 simpa only [List.length_nil,Nat.zero_add,List.nil_append,packedNumber] using congrArg numbersNumber hm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnRowProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnRowProof
