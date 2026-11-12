module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnRowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobDeletionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnDeletionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedAuxiliaryCoding NumberedMultisetNumeric
open OriginalHereditaryAgendaDefinitions OriginalHereditaryExpectedDefinitions OriginalHereditarySettledObserverDefinitions
open OriginalHereditaryExpectedReturnSupportProof OriginalHereditaryExpectedReturnRowProof
open OriginalHereditaryTypedJobDecorationProof OriginalHereditaryWorkBound OriginalRawSyntaxTransport
open OriginalHereditaryFiniteObserver

theorem expectedTermStep (R : Program 2) {n : Nat} {arity : Fin n → Nat} (c : Nat)
 (s : OriginalHereditaryNativeBoundDefinitions.State (Fin n) arity) {Gamma : List Ty}
 (q : Packed (Fin n) arity Gamma)
 (h : OriginalHereditaryNativeBoundDefinitions.Step s ⟨Gamma,q⟩) :
 Expected arity R c (termJob q)
   (rawValue (family R (OriginalHereditaryNativeBoundDefinitions.weight s)) q.1 c ⟨Gamma,termCode q.2⟩) := by
 have he := OriginalHereditarySettledObserverProof.stepNormalization R n arity c s ⟨Gamma,q⟩ h
 unfold rawValue
 rw [OriginalTypedDecoderReconstructionLocalProof.contextNumber]
 change Expected arity R c (termJob q) (OriginalHereditaryFiniteStability.value
   (family R (OriginalHereditaryNativeBoundDefinitions.weight s)) c ⟨Gamma,q⟩)
 rw [he]
 exact expectedTerm R c q

theorem deletionMember (R : Program 2) {n : Nat} {arity : Fin n → Nat} (c : Nat)
 (s : OriginalHereditaryNativeBoundDefinitions.State (Fin n) arity)
 (binders tail : List Ty) :
 ∀ (tau : Ty) (q : AuxTerm (Fin n) arity (binders ++ tail) tau),
 s = ⟨binders ++ tail,⟨tau,q⟩⟩ →
 ∀ t ∈ deletionsFrom (termCode q) binders tail,
 Expected arity R c (⟨0,typeNumber tau,t⟩ : Job n)
   (rawValue (family R (OriginalHereditaryNativeBoundDefinitions.weight s)) tau c t) := by
 induction tail generalizing binders with
 | nil => intro tau q hs t ht; simp [deletionsFrom] at ht
 | cons sigma tail ih =>
   intro tau q hs t ht
   simp only [deletionsFrom,List.mem_cons] at ht
   rcases ht with rfl | ht
   · rw [← OriginalRawSyntaxTransportTypedSupportProof.typedErasure binders tail sigma tau q]
     apply expectedTermStep R c s ⟨tau,substitute q (prefixErasure binders tail sigma)⟩
     rw [hs]
     exact OriginalHereditaryNativeBoundSliceProof.prefixDeletionStep n arity binders tail sigma tau q
   · have hh := ih (binders ++ [sigma])
     exact hh tau q hs t ht

theorem decoratedInherited {n c : Nat} (arity : Fin n → Nat) (R : Program 2) (a : Job n)
 (ss : List (State (Fin n))) (index : Nat) (f : State (Fin n) → Nat)
 (hi : arityValue (codeNumber a.core.code) ≤ index)
 (h : ∀ t ∈ ss, Expected arity R c (⟨a.role,a.typ,t⟩ : Job n) (f t)) :
 List.Forall₂ (Expected arity R c) (decorate c a index ss) (ss.map f) := by
 induction ss generalizing index with
 | nil => exact .nil
 | cons t ss ih =>
   rw [decorate,List.map_cons,childInherited a index t hi]
   exact .cons (h t (List.mem_cons_self))
     (ih (index+1) (by omega) (fun t ht => h t (List.mem_cons_of_mem _ ht)))

theorem termDeletionsExpected (R : Program 2) {n c : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
 (q : Packed (Fin n) arity Gamma) (index : Nat)
 (hi : arityValue (codeNumber (termCode q.2)) ≤ index) :
 List.Forall₂ (Expected arity R c)
   (decorate c (termJob q) index (deletionsFrom (termCode q.2) [] Gamma))
   ((deletionsFrom (termCode q.2) [] Gamma).map
     (rawValue (family R (OriginalHereditaryNativeBoundDefinitions.weight ⟨Gamma,q⟩)) q.1 c)) := by
 apply decoratedInherited arity R (termJob q) _ index _ hi
 exact deletionMember R c ⟨Gamma,q⟩ [] Gamma q.1 q.2 rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnDeletionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnDeletionProof
