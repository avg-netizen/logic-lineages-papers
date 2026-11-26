module
public import LogicLineages.PermittedControl.ActualInitialSignedCountCleanupTargets
import LogicLineages.PermittedControl.ActualShortCountCleanupProof
import LogicLineages.PermittedControl.ActualSymbolicZeroSuccessorMovedProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualInitialSignedCountCleanup
open MixedSameRankResidue (orderedReads actualSum WeightedOperand)
open ActualSymbolicZeroSuccessor (SyntaxState exactMovedAndCleanupSyntax cleanupShift cleanSyntax)
open ActualShortCountCleanup (retained shortShift exactShortCountCleanup)
open ActualReadChargeIteration (ReadState stateValue)
open ActualFiniteGlobalTail (syntaxOf)
open ActualZeroClassReplacement (liftedReads readSum)
open ActualBoundedSignedRouteSemantics (stateSyntax)

theorem exactOriginalInitialCleanup : ExactOriginalInitialCleanup := by
  intro f B selected ρ original live
  have actual := exactShortCountCleanup f B selected ρ original.constant original.reads original.reads live
  have literal := exactMovedAndCleanupSyntax.2 original.reads
  refine ⟨actual.1,?_,actual.2.1,?_,actual.2.2.2.2.symm⟩
  · change SyntaxState.mk (original.constant + shortShift original.reads)
        ((retained original.reads).map Prod.fst) =
      SyntaxState.mk (original.constant + cleanupShift (original.reads.map Prod.fst))
        (cleanSyntax (original.reads.map Prod.fst))
    rw [literal.1,literal.2]
  · intro t used
    obtain ⟨rd,inside,rfl⟩ := List.mem_map.mp used
    exact ⟨List.mem_map.mpr ⟨rd,actual.1.subset inside,rfl⟩,actual.2.2.1 rd inside⟩

private theorem valueListUnique (f ρ : Nat → Nat) (ts : List WeightedOperand) (vs ws : List Nat)
    (h : orderedReads f ρ ts vs) (k : orderedReads f ρ ts ws) : vs = ws := by
  induction ts generalizing vs ws with
  | nil =>
    cases vs <;> cases ws
    · rfl
    · exact False.elim k
    · exact False.elim h
    · exact False.elim h
  | cons t ts ih =>
    cases vs with
    | nil => exact False.elim h
    | cons v vs =>
      cases ws with
      | nil => exact False.elim k
      | cons w ws =>
        have here : v = w := Option.some.inj (Option.some.inj (h.2.1.symm.trans k.2.1))
        exact congrArg₂ List.cons here (ih vs ws h.2.2 k.2.2)

private theorem stateValueUnique (f ρ : Nat → Nat) (l r : ReadState)
    (frames : stateSyntax l = stateSyntax r) (left : liftedReads f ρ l.reads)
    (right : liftedReads f ρ r.reads) : stateValue l = stateValue r := by
  have const : l.constant = r.constant := congrArg SyntaxState.constant frames
  have terms : l.reads.map Prod.fst = r.reads.map Prod.fst := congrArg SyntaxState.terms frames
  have a : orderedReads f ρ (r.reads.map Prod.fst) (l.reads.map Prod.snd) := by
    rw [← terms]
    exact left
  have same := valueListUnique f ρ (r.reads.map Prod.fst) _ _ a right
  change l.constant + actualSum (l.reads.map Prod.fst) (l.reads.map Prod.snd) =
    r.constant + actualSum (r.reads.map Prod.fst) (r.reads.map Prod.snd)
  rw [const,terms,same]

theorem exactOriginalInitialCleanupTest : ExactOriginalInitialCleanupTest := by
  intro f B selected ρ s available test positive
  constructor
  · rintro ⟨original,frames,live,signed⟩
    have h := exactOriginalInitialCleanup f B selected ρ original live
    refine ⟨cleanupRead original,h.2.1.trans (congrArg cleanup frames),h.2.2.1,?_⟩
    rw [h.2.2.2.2]
    exact signed
  · rintro ⟨claimed,claims,liveClaimed,signed⟩
    obtain ⟨original,frames,live⟩ := available
    have h := exactOriginalInitialCleanup f B selected ρ original live
    have fmatch : stateSyntax claimed = stateSyntax (cleanupRead original) :=
      claims.trans (h.2.1.trans (congrArg cleanup frames)).symm
    have result := (stateValueUnique f ρ claimed (cleanupRead original) fmatch liveClaimed h.2.2.1).trans h.2.2.2.2
    exact ⟨original,frames,live,result ▸ signed⟩

end LogicLineages.PermittedControl.ActualInitialSignedCountCleanup
