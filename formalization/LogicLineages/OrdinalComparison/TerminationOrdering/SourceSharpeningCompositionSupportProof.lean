module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningCompositionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningCompositionSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding RecursiveComparison SourceSharpening

def CompositionMeaning {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (v : MarkedTerm Symbol arity Gamma tau) : Prop :=
  ∀ (q u : MarkedTerm Symbol arity Gamma tau), Sharp Symbol arity Gamma q u →
    Sharp Symbol arity Gamma u v → Sharp Symbol arity Gamma q v

def ArgumentsMeaning {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (args : Arguments Symbol arity Gamma types) : Prop :=
  (∀ p∈argumentList args,CompositionMeaning p.2) ∧
  ∀ (ss us : Arguments Symbol arity Gamma types),ArgumentsSharp Symbol arity Gamma ss us →
    ArgumentsSharp Symbol arity Gamma us args → ArgumentsSharp Symbol arity Gamma ss args

theorem extrasMember {Symbol : Type} {arity : Symbol → Nat} {Gamma sourceTypes types : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (sourceExtras : Arguments Symbol arity Gamma sourceTypes) (args : Arguments Symbol arity Gamma types)
    (h : ExtrasSharp Symbol arity Gamma f base sourceTypes sourceExtras args) :
    ∀ p∈argumentList args,ExtraSharp Symbol arity Gamma f base sourceTypes sourceExtras p := by
  induction types with
  | nil => cases args; intro p hp; cases hp
  | cons tau types ih =>
    cases args with
    | cons q rest =>
      cases h with
      | cons _ _ _ _ _ _ _ _ hq hr =>
        intro p hp
        rcases List.mem_cons.mp hp with he | hm
        · subst p; exact hq
        · exact ih rest hr p hm

theorem extraCompose {Symbol : Type} {arity : Symbol → Nat} {Gamma typesQ typesB : List Ty} {tau : Ty}
    (f : Head Symbol) (baseQ baseB : Arguments Symbol arity Gamma (headArguments arity f))
    (extrasQ : Arguments Symbol arity Gamma typesQ) (extrasB : Arguments Symbol arity Gamma typesB)
    (t : MarkedTerm Symbol arity Gamma tau) (IH : CompositionMeaning t)
    (hWhole : ∀ sigma,Sharp Symbol arity Gamma (.marked f sigma baseQ typesQ extrasQ) (.marked f sigma baseB typesB extrasB))
    (hQB : ExtrasSharp Symbol arity Gamma f baseQ typesQ extrasQ extrasB)
    (hBt : ExtraSharp Symbol arity Gamma f baseB typesB extrasB ⟨tau,t⟩) :
    ExtraSharp Symbol arity Gamma f baseQ typesQ extrasQ ⟨tau,t⟩ := by
  cases hBt with
  | existing _ _ _ _ _ s _ hm hs =>
    have hQs := extrasMember f baseQ extrasQ extrasB hQB ⟨tau,s⟩ hm
    cases hQs with
    | existing _ _ _ _ _ q _ hq hqs =>
      exact .existing f baseQ typesQ extrasQ tau q t hq (IH q s hqs hs)
    | whole _ _ _ _ _ _ hqs =>
      exact .whole f baseQ typesQ extrasQ tau t (IH _ s hqs hs)
  | whole _ _ _ _ _ _ hBt =>
    exact .whole f baseQ typesQ extrasQ tau t (IH _ _ (hWhole tau) hBt)

theorem extrasCompose {Symbol : Type} {arity : Symbol → Nat} {Gamma typesQ typesB typesT : List Ty}
    (f : Head Symbol) (baseQ baseB : Arguments Symbol arity Gamma (headArguments arity f))
    (extrasQ : Arguments Symbol arity Gamma typesQ) (extrasB : Arguments Symbol arity Gamma typesB)
    (target : Arguments Symbol arity Gamma typesT)
    (hWhole : ∀ sigma,Sharp Symbol arity Gamma (.marked f sigma baseQ typesQ extrasQ) (.marked f sigma baseB typesB extrasB))
    (hQB : ExtrasSharp Symbol arity Gamma f baseQ typesQ extrasQ extrasB)
    (hBT : ExtrasSharp Symbol arity Gamma f baseB typesB extrasB target)
    (IH : ∀ p∈argumentList target,CompositionMeaning p.2) :
    ExtrasSharp Symbol arity Gamma f baseQ typesQ extrasQ target := by
  induction typesT with
  | nil => cases target; exact .nil _ _ _ _
  | cons tau types ih =>
    cases target with
    | cons q rest =>
      cases hBT with
      | cons _ _ _ _ _ _ _ _ hq hr =>
        exact .cons f baseQ typesQ extrasQ tau types q rest
          (extraCompose f baseQ baseB extrasQ extrasB q (IH _ (List.mem_cons_self ..)) hWhole hQB hq)
          (ih rest hr (fun p hp => IH p (List.mem_cons_of_mem _ hp)))

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningCompositionSupportProof
