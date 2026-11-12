module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteStabilityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedJointDepthProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedAuxiliaryCoding NumberedMultisetNumeric
open OriginalHereditaryAgendaDefinitions OriginalHereditarySettledObserverDefinitions
open OriginalHereditaryExpectedDefinitions OriginalHereditaryExpectedTargets
open OriginalHereditaryFiniteObserver OriginalHereditaryFiniteStability OriginalHereditaryNativeBoundDefinitions

theorem memberSum (xs : List Nat) (a : Nat) (ha : a ∈ xs) : a ≤ xs.sum := by
 induction xs with
 | nil => simp at ha
 | cons x xs ih =>
   rcases List.mem_cons.mp ha with rfl | ht
   · simp
   · have hh := ih ht
     simp only [List.sum_cons]
     omega

theorem memberWeight {n : Nat} {arity : Fin n → Nat} {Gamma types : List Ty}
 (args : AuxArguments (Fin n) arity Gamma types) (q : Packed (Fin n) arity Gamma)
 (hq : q ∈ argumentList args) : weight ⟨Gamma,q⟩ ≤ argumentDepth args := by
 exact memberSum _ _ (List.mem_map.mpr ⟨q,hq,rfl⟩)

theorem argumentsAtDepth (R : Program 2) {n : Nat} {arity : Fin n → Nat}
 {Gamma types : List Ty} (c : Nat) (args : AuxArguments (Fin n) arity Gamma types)
 (depth : Nat) (h : ∀ q ∈ argumentList args, weight ⟨Gamma,q⟩ ≤ depth) :
 OriginalRootObservation.argumentValues (family R depth) c args = argumentValues R c args := by
 apply List.map_congr_left
 intro q hq
 apply congrArg (Nat.pair (typeNumber q.1))
 exact OriginalHereditaryFiniteStabilityProof.settled R n arity c ⟨Gamma,q⟩ depth (h q hq)

theorem argumentsJointDepth : ArgumentsJointDepth := by
 intro R n arity Gamma types c args depth h
 apply List.map_congr_left
 intro q hq
 apply congrArg (Nat.pair (typeNumber q.1))
 exact OriginalHereditaryFiniteStabilityProof.settled R n arity c ⟨Gamma,q⟩ depth
   (Nat.le_trans (memberWeight args q hq) h)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedJointDepthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedJointDepthProof
