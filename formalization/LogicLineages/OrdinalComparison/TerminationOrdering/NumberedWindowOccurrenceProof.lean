module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowOccurrenceTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowOccurrenceProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowReduction NumberedWindowTraces NumberedWindowOccurrenceTargets

theorem pointwiseTupleTarget : NumberedWindowOccurrenceTargets.ActualPointwiseTupleTarget := by
  intro Symbol arity symbols S above Gamma types args values h
  induction types generalizing values with
  | nil => cases args; cases h; exact ⟨0,.nil,rfl,.equivalent .nil⟩
  | cons sigma types ih => cases args with
    | cons q rest => cases h with
      | @cons _ R _ values hq hr =>
        rcases R with ⟨tau,R⟩
        obtain ⟨m,hm⟩ := hq
        have ht : sigma=tau := NumberedPrimaryEquivalenceProof.traceTypePreservation Symbol arity above Gamma m _ _ (NumberedWindowTracesProof.packedErasure Symbol arity symbols S above Gamma m _ _ hm)
        cases ht
        obtain ⟨n,target,he,htarget⟩ := ih rest values hr
        exact ⟨m+n,.cons R target,congrArg (List.cons (⟨sigma,R⟩ : Packed Symbol arity Gamma)) he,
          NumberedWindowTracesProof.tupleCons Symbol arity symbols S above Gamma types sigma m n q R rest target
            ((NumberedWindowTracesProof.typedPresentation Symbol arity symbols S above Gamma sigma m q R).mp hm) htarget⟩

theorem pointwiseTupleSource : ActualPointwiseTupleSource := by
  intro Symbol arity symbols S above Gamma types target values h
  induction types generalizing values with
  | nil => cases target; cases h; exact ⟨0,.nil,rfl,.equivalent .nil⟩
  | cons sigma types ih => cases target with
    | cons q rest => cases h with
      | @cons R _ values _ hq hr =>
        rcases R with ⟨tau,R⟩
        obtain ⟨m,hm⟩ := hq
        have ht : tau=sigma := NumberedPrimaryEquivalenceProof.traceTypePreservation Symbol arity above Gamma m _ _
          (NumberedWindowTracesProof.packedErasure Symbol arity symbols S above Gamma m _ _ hm)
        cases ht
        obtain ⟨n,source,he,hsource⟩ := ih rest values hr
        exact ⟨m+n,.cons R source,congrArg (List.cons (⟨sigma,R⟩ : Packed Symbol arity Gamma)) he,
          NumberedWindowTracesProof.tupleCons Symbol arity symbols S above Gamma types sigma m n R q source rest
            ((NumberedWindowTracesProof.typedPresentation Symbol arity symbols S above Gamma sigma m R q).mp hm) hsource⟩

theorem finiteMarkStep : ActualFiniteMarkStep := by
  intro Symbol arity symbols S above n Gamma tau q
  induction q using AuxTerm.rec (motive_2 := fun _ _ _ => True)
  case var v => intro r he; cases he
  case lam body ih =>
    intro r he
    simp only [finiteMark,Option.map_eq_some_iff] at he
    obtain ⟨b,hb,rfl⟩ := he
    exact .lam body b (ih b hb)
  case app q a ihq iha => intro r he; cases he
  case bottom tau => intro r he; cases he
  case ordinary f base ih =>
    intro r he
    cases he
    exact .put n f base
  case numbered k f tau base types extras ihb ihe => intro r he; cases he
  case nil => trivial
  case cons => trivial

theorem originalPositiveMark : ActualOriginalPositiveMark := by
  intro Symbol arity symbols S above n Gamma tau q r hm Q hQ
  obtain ⟨R,hmark,hR⟩ := NumberedRepresentationRigidityProof.finiteMarkWitness Symbol arity n Gamma tau q r hm Q hQ
  exact ⟨R,finiteMarkStep Symbol arity symbols S above n Gamma tau Q R hmark,hR⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowOccurrenceProof
