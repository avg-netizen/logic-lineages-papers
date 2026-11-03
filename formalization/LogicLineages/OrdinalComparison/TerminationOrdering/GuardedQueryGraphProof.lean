module
public import LogicLineages.OrdinalComparison.TerminationOrdering.GuardedQueryGraphFrameProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.GuardedQueryGraphProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open Source.SourceTypeSupport Source.SourceFreeOccurrences Source.SourcePortContexts Source.SourceOpenedObservations
open RecursiveComparison ComparisonFreeVariables FiniteQueryPrimitives GuardedQueryGraph

theorem stepPreservesFrame : GuardedQueryGraphTargets.StepPreservesFrame := GuardedQueryGraphFrameProof.stepPreservesFrame
theorem freshOpeningAvailability : GuardedQueryGraphTargets.FreshOpeningAvailability := GuardedQueryGraphSupportProof.freshOpeningAvailability

theorem reachableFrame : GuardedQueryGraphTargets.ReachableFrame := by
  intro Symbol arity above Γ σ τ s t mode q h
  induction h with
  | root =>
      have hi := (FiniteQueryPrimitivesProof.initialFrame Symbol arity Γ σ τ s t).2
      exact ⟨hi.1,hi.2.1,hi.2.2.1,t,rfl,hi.2.2.2⟩
  | step h edge ih => exact stepPreservesFrame Symbol arity above Γ σ τ s t _ _ ih edge

theorem weakMatchPair {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Γ : List Ty} {ss ts : List (Packed Symbol arity Γ)}
    (h : WeakMatch Symbol arity above Γ ss ts) (s t : Packed Symbol arity Γ)
    (hp : (s,t) ∈ ss.zip ts) : Weak Symbol arity above Γ s t := by
  induction ss generalizing ts with
  | nil => simp at hp
  | cons a rest ih =>
      cases h with
      | cons a b rest tail hab hrest =>
          rcases List.mem_cons.mp hp with he | ht
          · cases he; exact hab
          · exact ih hrest ht

theorem replacementWitness {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Γ : List Ty} {removed inserted : List (Packed Symbol arity Γ)}
    (h : ReplacementMatch Symbol arity above Γ removed inserted) :
    ∀ t ∈ inserted,∃ s ∈ removed,Strict Symbol arity above Γ s t := by
  induction inserted with
  | nil => simp
  | cons t rest ih =>
      cases h with
      | cons removed s t rest hs hst hr =>
          intro p hp
          rcases List.mem_cons.mp hp with he | ht
          · subst p; exact ⟨s,hs,hst⟩
          · exact ih hr p ht

theorem funPremisesCovered : GuardedQueryGraphTargets.FunPremisesCovered := by
  intro Symbol arity above Γ B P f g ss ts matched he ht hp hm s t hmem
  exact ⟨weakMatchPair hm s t hmem,Step.funPair P f g ss ts matched s t he ht hp hmem⟩

theorem statPremisesCovered : GuardedQueryGraphTargets.StatPremisesCovered := by
  intro Symbol arity above Γ B P f g base types extras ts he hm
  cases hm with
  | replace ss ts kept retained removed inserted hp hq hn hw hr =>
      refine ⟨kept,retained,removed,inserted,hp,hq,hn,?_,?_⟩
      · intro s t hmem
        exact ⟨weakMatchPair hw s t hmem,Step.statRetained P f g base types extras _ kept retained removed inserted s t he hp hq hn hmem⟩
      · intro t ht
        obtain ⟨s,hs,hst⟩ := replacementWitness hr t ht
        exact ⟨s,hs,hst,Step.statReplaced P f g base types extras _ kept retained removed inserted s t he hp hq hn hs ht⟩

theorem issuedSelectExecutionsBounded : GuardedQueryGraphTargets.IssuedSelectExecutionsBounded := by
  intro Symbol arity above Γ σ τ s t mode q issued d hreach hexec
  have hf := reachableFrame Symbol arity above Γ σ τ s t mode q hreach
  have hc := (FiniteQueryPrimitivesProof.initialFrame Symbol arity Γ σ τ s t).1
  have hk := hf.1
  have hp := hf.2.1
  have ha := hf.2.2.1
  rw [issued.sourceEquation] at hk hp ha
  exact OriginalApplicationTraceProof.everySelectExecution Symbol arity _ _ _ _ issued.head issued.base issued.extraTypes
    issued.extras q.target.1 issued.request d hc hk hp ha hexec

end LogicLineages.OrdinalComparison.TerminationOrdering.GuardedQueryGraphProof
