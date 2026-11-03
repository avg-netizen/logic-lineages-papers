module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceContextsTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceContextsProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence NumberedTraceContexts

theorem packedToTyped {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {n : Nat} {q r : Packed Symbol arity Gamma}
    (h : Trace Symbol arity above Gamma n q r) : ∀ (tau : Ty) (Q R : AuxTerm Symbol arity Gamma tau),
      q=⟨tau,Q⟩ → r=⟨tau,R⟩ → TypedTrace Symbol arity above Gamma tau n Q R := by
  induction h with
  | equivalent h =>
    intro tau Q R hq hr
    rw [hq,hr] at h
    exact .equivalent h
  | @raw sigma q r h =>
    intro tau Q R hq hr
    have ht : sigma=tau := congrArg Sigma.fst hq
    cases ht
    have hq' : q=Q := by injection hq
    have hr' : r=R := by injection hr
    subst Q
    subst R
    exact .raw h
  | @trans m n q r s h₁ h₂ ih₁ ih₂ =>
    intro tau Q S hq hs
    have hr : r.1=tau := (NumberedPrimaryEquivalenceProof.traceTypePreservation Symbol arity above Gamma m q r h₁).symm.trans
      (congrArg Sigma.fst hq)
    rcases r with ⟨rho,R⟩
    cases hr
    exact .trans (ih₁ _ Q R hq rfl) (ih₂ _ R S rfl hs)

theorem typedToPacked {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {tau : Ty} {n : Nat} {q r : AuxTerm Symbol arity Gamma tau}
    (h : TypedTrace Symbol arity above Gamma tau n q r) : Trace Symbol arity above Gamma n ⟨tau,q⟩ ⟨tau,r⟩ := by
  induction h with
  | equivalent h => exact .equivalent h
  | raw h => exact .raw _ _ h
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem typedPresentation : NumberedTraceContextsTargets.ActualTypedPresentation := by
  intro Symbol arity above Gamma tau n q r
  exact ⟨fun h => packedToTyped h tau q r rfl rfl,typedToPacked⟩

theorem lambdaContext : NumberedTraceContextsTargets.ActualLambdaContext := by
  intro Symbol arity above Gamma sigma tau n q r h
  induction h with
  | @equivalent q r h => exact .equivalent (.lam q r h)
  | @raw q r h => exact .raw (.lam q r h)
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem functionContext : NumberedTraceContextsTargets.ActualFunctionContext := by
  intro Symbol arity above Gamma sigma tau n q r a h
  induction h with
  | @equivalent q r h => exact .equivalent (.appFunction q r a h)
  | @raw q r h => exact .raw (.appFunction q r a h)
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem argumentReflexivity {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (args : AuxArguments Symbol arity Gamma types) : ArgumentPrimary Symbol arity Gamma types args args := by
  induction types with
  | nil => cases args; exact .nil
  | cons sigma types ih => cases args with
    | cons q rest => exact .cons q q rest rest (.refl _) (ih rest)

theorem tupleHead {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma types : List Ty} {sigma : Ty} {n : Nat} {q r : AuxTerm Symbol arity Gamma sigma}
    (h : TypedTrace Symbol arity above Gamma sigma n q r) (rest : AuxArguments Symbol arity Gamma types) :
    TupleTrace Symbol arity above Gamma (sigma::types) n (.cons q rest) (.cons r rest) := by
  induction h with
  | @equivalent q r h => exact .equivalent (.cons q r rest rest h (argumentReflexivity rest))
  | @raw q r h => exact .raw (.head q r rest h)
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem tupleTail {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma types : List Ty} {sigma : Ty} {n : Nat} (q : AuxTerm Symbol arity Gamma sigma)
    {rest target : AuxArguments Symbol arity Gamma types} (h : TupleTrace Symbol arity above Gamma types n rest target) :
    TupleTrace Symbol arity above Gamma (sigma::types) n (.cons q rest) (.cons q target) := by
  induction h with
  | @equivalent rest target h => exact .equivalent (.cons q q rest target (.refl _) h)
  | @raw rest target h => exact .raw (.tail q rest target h)
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem tupleCons : NumberedTraceContextsTargets.ActualTupleCons := by
  intro Symbol arity above Gamma types sigma m n q r rest target hq hr
  exact .trans (tupleHead hq rest) (tupleTail r hr)

theorem ordinaryContext : NumberedTraceContextsTargets.ActualOrdinaryContext := by
  intro Symbol arity above Gamma f n base target h
  induction h with
  | @equivalent base target h => exact .equivalent (.ordinaryArguments f base target h)
  | @raw base target h => exact .raw (.ordinaryArguments f base target h)
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem numberedBaseContext : NumberedTraceContextsTargets.ActualNumberedBaseContext := by
  intro Symbol arity above Gamma k f tau n base target types extras h
  induction h with
  | @equivalent base target h => exact .equivalent (.numberedBase k f tau base target types extras h)
  | @raw base target h => exact .raw (.numberedBase k f tau base target types extras h)
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem numberedExtrasContext : NumberedTraceContextsTargets.ActualNumberedExtrasContext := by
  intro Symbol arity above Gamma k f tau n base types extras target h
  induction h with
  | @equivalent extras target h => exact .equivalent (.numberedExtras k f tau base types extras target h)
  | @raw extras target h => exact .raw (.numberedExtras k f tau base types extras target h)
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceContextsProof
