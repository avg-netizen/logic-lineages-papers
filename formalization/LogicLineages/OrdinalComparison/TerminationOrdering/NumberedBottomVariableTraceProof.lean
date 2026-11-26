module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariablePrimaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableStepProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableTraceProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimarySubstitution
open NumberedBottomVariable NumberedWindowTraces
open NumberedBottomVariableExchangeSupportProof NumberedBottomVariableStepProof

theorem traceInverse {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty}
    {above : Symbol → Symbol → Prop} {Gamma Delta : List Ty}
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta) (ht : BottomOrVariable theta)
    {count : Nat} {a b : Packed Symbol arity Delta}
    (h : WindowTrace Symbol arity symbols S above Delta count a b) :
    ∀ q : Packed Symbol arity Gamma, substitutePacked theta q = a →
      ∃ q' : Packed Symbol arity Gamma,
        WindowTrace Symbol arity symbols S above Gamma count q q' ∧ substitutePacked theta q' = b := by
  induction h with
  | equivalent hp =>
    intro q hq
    rw [← hq] at hp
    obtain ⟨q',hp',he⟩ := NumberedBottomVariablePrimaryProof.actualPrimaryInverse
      Symbol arity symbols S Gamma Delta theta ht q _ hp
    exact ⟨q',.equivalent hp',he⟩
  | raw source target hs =>
    intro q hq
    obtain ⟨source',hsource,he⟩ := typedWitness theta (fun p => p = q) _ source ⟨q,rfl,hq⟩
    subst q
    rw [← he] at hs
    obtain ⟨target',hstep,he'⟩ := stepInverse symbols S above source' Delta theta ht target hs
    exact ⟨⟨_,target'⟩,.raw source' target' hstep,
      congrArg (fun t => (⟨_,t⟩ : Packed Symbol arity Delta)) he'⟩
  | trans h₁ h₂ ih₁ ih₂ =>
    intro q hq
    obtain ⟨middle,hmiddle,he⟩ := ih₁ q hq
    obtain ⟨target,htarget,he'⟩ := ih₂ middle he
    exact ⟨target,.trans hmiddle htarget,he'⟩

theorem actualTraceInverse : NumberedBottomVariableLiftingTargets.ActualTraceInverse := by
  intro Symbol arity symbols S above Gamma Delta theta ht count q r h
  exact traceInverse theta ht h q rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableTraceProof
