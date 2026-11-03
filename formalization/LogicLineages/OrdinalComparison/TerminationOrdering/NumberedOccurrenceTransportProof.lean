module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOccurrenceTransportTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOccurrenceTransportProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence NumberedTraceContexts NumberedOccurrenceTransport

theorem argumentsToList : NumberedOccurrenceTransportTargets.ActualArgumentsToList := by
  intro Symbol arity n Gamma types args values h
  induction types with
  | nil => cases h; exact .nil
  | cons sigma types ih => cases h with
    | cons q Q rest values hq hr => exact .cons ⟨Q,rfl,hq⟩ (ih rest values hr)

theorem listToArguments : NumberedOccurrenceTransportTargets.ActualListToArguments := by
  intro Symbol arity n Gamma types args values h
  induction types generalizing values with
  | nil => cases args; cases h; exact ⟨.nil,rfl,.nil⟩
  | cons sigma types ih => cases args with
    | cons q rest => cases h with
      | cons hq hr =>
        obtain ⟨Q,rfl,hQ⟩ := hq
        obtain ⟨target,he,ht⟩ := ih rest _ hr
        exact ⟨.cons Q target,congrArg (List.cons (⟨sigma,Q⟩ : Packed Symbol arity Gamma)) he,.cons _ _ _ _ hQ ht⟩

theorem permuteRelation {alpha beta : Type} (R : alpha → beta → Prop) {qs rs : List alpha}
    (hp : qs.Perm rs) : ∀ values,List.Forall₂ R qs values → ∃ target,values.Perm target ∧ List.Forall₂ R rs target := by
  induction hp with
  | nil => intro values h; cases h; exact ⟨[],.nil,.nil⟩
  | cons q hp ih =>
    intro values h
    cases h with
    | cons hq hr =>
      obtain ⟨target,ht,hrel⟩ := ih _ hr
      exact ⟨_::target,.cons _ ht,.cons hq hrel⟩
  | swap q r rest =>
    intro values h
    cases h with
    | cons hq hr => cases hr with
      | cons hh ht => exact ⟨_::_::_,.swap _ _ _,.cons hh (.cons hq ht)⟩
  | trans hp₁ hp₂ ih₁ ih₂ =>
    intro values h
    obtain ⟨middle,hm,hrel⟩ := ih₁ values h
    obtain ⟨target,ht,hrel'⟩ := ih₂ middle hrel
    exact ⟨target,hm.trans ht,hrel'⟩

theorem permutationTransport : NumberedOccurrenceTransportTargets.ActualPermutationTransport := by
  intro Symbol arity n Gamma qs rs values hp h
  exact permuteRelation (PackedRep n) hp values h

theorem splitTransport : NumberedOccurrenceTransportTargets.ActualSplitTransport := by
  intro Symbol arity n Gamma qs rs values h
  induction qs generalizing values with
  | nil => exact ⟨[],values,rfl,.nil,h⟩
  | cons q qs ih => cases h with
    | cons hq hr =>
      obtain ⟨first,last,he,hfirst,hlast⟩ := ih _ hr
      exact ⟨_::first,last,congrArg (_::·) he,.cons hq hfirst,hlast⟩

theorem listBudgetLowering : NumberedOccurrenceTransportTargets.ActualListBudgetLowering := by
  intro Symbol arity n m hmn Gamma qs values h
  induction h with
  | nil => exact .nil
  | @cons q Q qs values hq hr ih =>
    obtain ⟨A,rfl,hA⟩ := hq
    exact .cons ⟨A,rfl,NumberedRewriteSyntaxProof.budgetLowering Symbol arity n m hmn Gamma q.1 q.2 A hA⟩ ih

theorem pointwiseTupleTrace : NumberedOccurrenceTransportTargets.ActualPointwiseTupleTrace := by
  intro Symbol arity above Gamma types args values h
  induction types generalizing values with
  | nil => cases args; cases h; exact ⟨0,.nil,rfl,.equivalent .nil⟩
  | cons sigma types ih => cases args with
    | cons q rest => cases h with
      | @cons _ R _ values hq hr =>
        rcases R with ⟨tau,R⟩
        obtain ⟨m,hm⟩ := hq
        have ht : sigma=tau := NumberedPrimaryEquivalenceProof.traceTypePreservation Symbol arity above Gamma m _ _ hm
        cases ht
        obtain ⟨n,target,he,htarget⟩ := ih rest values hr
        exact ⟨m+n,.cons R target,congrArg (List.cons (⟨sigma,R⟩ : Packed Symbol arity Gamma)) he,
          NumberedTraceContextsProof.tupleCons Symbol arity above Gamma types sigma m n q R rest target
            ((NumberedTraceContextsProof.typedPresentation Symbol arity above Gamma sigma m q R).mp hm) htarget⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOccurrenceTransportProof
