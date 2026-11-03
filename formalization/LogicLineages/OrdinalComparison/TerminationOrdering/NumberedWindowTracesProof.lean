module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowTracesTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowTracesProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedUniverseBindingTargets NumberedUniverseOperationsTargets NumberedWindowReduction NumberedWindowEquivalence NumberedWindowTraces

theorem packedErasure : NumberedWindowTracesTargets.ActualPackedErasure := by
  intro Symbol arity symbols S above Gamma n q r h
  induction h with
  | equivalent h => exact .equivalent (NumberedWindowEquivalenceProof.actualPrimaryErasure Symbol arity symbols S Gamma _ _ h)
  | raw q r h => exact .raw q r (NumberedWindowReductionProof.actualStepErasure Symbol arity symbols S above Gamma _ q r h)
  | trans h k ih ik => exact .trans ih ik

theorem tupleErasure : NumberedWindowTracesTargets.ActualTupleErasure := by
  intro Symbol arity symbols S above Gamma types n a b h
  induction h with
  | equivalent h => exact .equivalent (NumberedWindowEquivalenceProof.actualArgumentErasure Symbol arity symbols S Gamma types _ _ h)
  | raw h => exact .raw (NumberedWindowReductionProof.actualArgumentErasure Symbol arity symbols S above Gamma types _ _ h)
  | trans h k ih ik => exact .trans ih ik

theorem packedToTyped {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {n : Nat} {q r : Packed Symbol arity Gamma}
    (h : WindowTrace Symbol arity symbols S above Gamma n q r) : ∀ (tau : Ty) (Q R : AuxTerm Symbol arity Gamma tau),
      q=⟨tau,Q⟩ → r=⟨tau,R⟩ → WindowTypedTrace Symbol arity symbols S above Gamma tau n Q R := by
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
    intro tau Q T hq hs
    have hr : r.1=tau := (NumberedPrimaryEquivalenceProof.traceTypePreservation Symbol arity above Gamma m q r (packedErasure Symbol arity symbols S above Gamma m q r h₁)).symm.trans
      (congrArg Sigma.fst hq)
    rcases r with ⟨rho,R⟩
    cases hr
    exact .trans (ih₁ _ Q R hq rfl) (ih₂ _ R T rfl hs)

theorem typedToPacked {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {tau : Ty} {n : Nat} {q r : AuxTerm Symbol arity Gamma tau}
    (h : WindowTypedTrace Symbol arity symbols S above Gamma tau n q r) : WindowTrace Symbol arity symbols S above Gamma n ⟨tau,q⟩ ⟨tau,r⟩ := by
  induction h with
  | equivalent h => exact .equivalent h
  | raw h => exact .raw _ _ h
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem typedPresentation : NumberedWindowTracesTargets.ActualTypedPresentation := by
  intro Symbol arity symbols S above Gamma tau n q r
  exact ⟨fun h => packedToTyped h tau q r rfl rfl,typedToPacked⟩

theorem lambdaContext : NumberedWindowTracesTargets.ActualLambdaContext := by
  intro Symbol arity symbols S above Gamma sigma tau n q r h
  induction h with
  | @equivalent q r h => exact .equivalent (.lam q r h)
  | @raw q r h => exact .raw (.lam q r h)
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem functionContext : NumberedWindowTracesTargets.ActualFunctionContext := by
  intro Symbol arity symbols S above Gamma sigma tau n q r a h
  induction h with
  | @equivalent q r h => exact .equivalent (.appFunction q r a h)
  | @raw q r h => exact .raw (.appFunction q r a h)
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem argumentReflexivity {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty} {Gamma types : List Ty}
    (args : AuxArguments Symbol arity Gamma types) : WindowArgumentPrimary Symbol arity symbols S Gamma types args args := by
  induction types with
  | nil => cases args; exact .nil
  | cons sigma types ih => cases args with
    | cons q rest => exact .cons q q rest rest (.refl _) (ih rest)

theorem tupleHead {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty} {above : Symbol → Symbol → Prop}
    {Gamma types : List Ty} {sigma : Ty} {n : Nat} {q r : AuxTerm Symbol arity Gamma sigma}
    (h : WindowTypedTrace Symbol arity symbols S above Gamma sigma n q r) (rest : AuxArguments Symbol arity Gamma types) :
    WindowTupleTrace Symbol arity symbols S above Gamma (sigma::types) n (.cons q rest) (.cons r rest) := by
  induction h with
  | @equivalent q r h => exact .equivalent (.cons q r rest rest h (argumentReflexivity rest))
  | @raw q r h => exact .raw (.head q r rest h)
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem tupleTail {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty} {above : Symbol → Symbol → Prop}
    {Gamma types : List Ty} {sigma : Ty} {n : Nat} (q : AuxTerm Symbol arity Gamma sigma)
    {rest target : AuxArguments Symbol arity Gamma types} (h : WindowTupleTrace Symbol arity symbols S above Gamma types n rest target) :
    WindowTupleTrace Symbol arity symbols S above Gamma (sigma::types) n (.cons q rest) (.cons q target) := by
  induction h with
  | @equivalent rest target h => exact .equivalent (.cons q q rest target (.refl _) h)
  | @raw rest target h => exact .raw (.tail q rest target h)
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem tupleCons : NumberedWindowTracesTargets.ActualTupleCons := by
  intro Symbol arity symbols S above Gamma types sigma m n q r rest target hq hr
  exact .trans (tupleHead hq rest) (tupleTail r hr)

theorem ordinaryContext : NumberedWindowTracesTargets.ActualOrdinaryContext := by
  intro Symbol arity symbols S above Gamma f n base target h
  induction h with
  | @equivalent base target h => exact .equivalent (.ordinaryArguments f base target h)
  | @raw base target h => exact .raw (.ordinaryArguments f base target h)
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem numberedBaseContext : NumberedWindowTracesTargets.ActualNumberedBaseContext := by
  intro Symbol arity symbols S above Gamma k f tau n base target types extras h
  induction h with
  | @equivalent base target h => exact .equivalent (.numberedBase k f tau base target types extras h)
  | @raw base target h => exact .raw (.numberedBase k f tau base target types extras h)
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem numberedExtrasContext : NumberedWindowTracesTargets.ActualNumberedExtrasContext := by
  intro Symbol arity symbols S above Gamma k f tau n base types extras target h
  induction h with
  | @equivalent extras target h => exact .equivalent (.numberedExtras k f tau base types extras target h)
  | @raw extras target h => exact .raw (.numberedExtras k f tau base types extras target h)
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem endpoint {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty}
    (hc : SubtypeClosed (fun t => t∈S)) {above : Symbol → Symbol → Prop} {Gamma : List Ty} {n : Nat}
    {q r : Packed Symbol arity Gamma} (h : WindowTrace Symbol arity symbols S above Gamma n q r) :
    PackedGood (fun t => t∈S) (HeadInWindow arity symbols S) q →
    PackedGood (fun t => t∈S) (HeadInWindow arity symbols S) r := by
  induction h with
  | equivalent h => exact (NumberedWindowEquivalenceProof.actualPrimaryConfinement Symbol arity symbols S Gamma _ _ h).mp
  | raw q r h => exact NumberedWindowReductionProof.actualStepConfinement Symbol arity symbols S hc above Gamma _ q r h
  | trans h k ih ik => exact fun hg => ik (ih hg)

theorem tupleEndpoint {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty}
    (hc : SubtypeClosed (fun t => t∈S)) {above : Symbol → Symbol → Prop} {Gamma types : List Ty} {n : Nat}
    {a b : AuxArguments Symbol arity Gamma types} (h : WindowTupleTrace Symbol arity symbols S above Gamma types n a b) :
    GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) a →
    GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) b := by
  induction h with
  | equivalent h => exact (NumberedWindowEquivalenceProof.actualArgumentConfinement Symbol arity symbols S Gamma types _ _ h).mp
  | raw h => exact NumberedWindowReductionProof.actualArgumentConfinement Symbol arity symbols S hc above Gamma types _ _ h
  | trans h k ih ik => exact fun hg => ik (ih hg)

theorem boundaryGood {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty}
    (hc : SubtypeClosed (fun t => t∈S)) {above : Symbol → Symbol → Prop} {Gamma : List Ty} {n : Nat}
    {q r p : Packed Symbol arity Gamma} {h : WindowTrace Symbol arity symbols S above Gamma n q r}
    (hb : Boundary h p) : PackedGood (fun t => t∈S) (HeadInWindow arity symbols S) q →
    PackedGood (fun t => t∈S) (HeadInWindow arity symbols S) p := by
  induction hb with
  | start h => exact id
  | finish h => exact endpoint hc h
  | left h k hb ih => exact ih
  | right h k hb ih => exact fun hg => ih (endpoint hc h hg)

theorem tupleBoundaryGood {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty}
    (hc : SubtypeClosed (fun t => t∈S)) {above : Symbol → Symbol → Prop} {Gamma types : List Ty} {n : Nat}
    {a b p : AuxArguments Symbol arity Gamma types} {h : WindowTupleTrace Symbol arity symbols S above Gamma types n a b}
    (hb : TupleBoundary h p) : GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) a →
    GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) p := by
  induction hb with
  | start h => exact id
  | finish h => exact tupleEndpoint hc h
  | left h k hb ih => exact ih
  | right h k hb ih => exact fun hg => ih (tupleEndpoint hc h hg)

theorem allBoundaries : NumberedWindowTracesTargets.ActualAllBoundaries := by
  intro Symbol arity symbols S hc above Gamma n q r h hg p hp
  exact boundaryGood hc hp hg

theorem allTupleBoundaries : NumberedWindowTracesTargets.ActualAllTupleBoundaries := by
  intro Symbol arity symbols S hc above Gamma types n a b h hg p hp
  exact tupleBoundaryGood hc hp hg

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowTracesProof
