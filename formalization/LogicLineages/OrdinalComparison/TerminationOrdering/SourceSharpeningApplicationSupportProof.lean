module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningApplicationTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningApplicationSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding RecursiveComparison SourceSharpening

theorem listAppend {Symbol : Type} {arity : Symbol → Nat} {Gamma xs ys : List Ty}
    (a : Arguments Symbol arity Gamma xs) (b : Arguments Symbol arity Gamma ys) :
    argumentList (appendArguments a b)=argumentList a++argumentList b := by
  induction xs with
  | nil => cases a; rfl
  | cons tau xs ih =>
    cases a with
    | cons q rest => exact congrArg (List.cons ⟨tau,q⟩) (ih rest)

theorem argumentsSubstitute {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta types : List Ty}
    (ss ts : Arguments Symbol arity Gamma types) (h : ArgumentsSharp Symbol arity Gamma ss ts)
    (theta eta : MarkedSubstitution Symbol arity Gamma Delta)
    (H : ∀ tau (v : Variable Gamma tau),Sharp Symbol arity Delta (theta v) (eta v)) :
    ArgumentsSharp Symbol arity Delta (substituteArguments ss theta) (substituteArguments ts eta) := by
  induction types with
  | nil => cases ss; cases ts; exact .nil
  | cons tau types ih =>
    cases h with
    | cons s t ss ts hs hr =>
      exact .cons _ _ _ _
        (SourceSharpeningSubstitutionProof.relatedSubstitution Symbol arity Gamma Delta tau s t theta eta hs H)
        (ih ss ts hr)

theorem extraSubstitute {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta sourceTypes : List Ty} {tau : Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (extras : Arguments Symbol arity Gamma sourceTypes) (t : MarkedTerm Symbol arity Gamma tau)
    (h : ExtraSharp Symbol arity Gamma f base sourceTypes extras ⟨tau,t⟩)
    (theta eta : MarkedSubstitution Symbol arity Gamma Delta)
    (H : ∀ tau (v : Variable Gamma tau),Sharp Symbol arity Delta (theta v) (eta v)) :
    ExtraSharp Symbol arity Delta f (substituteArguments base theta) sourceTypes
      (substituteArguments extras theta) ⟨tau,substituteTerm t eta⟩ := by
  cases h with
  | existing _ _ _ _ _ s _ hm hs =>
    apply ExtraSharp.existing _ _ _ _ tau (substituteTerm s theta) (substituteTerm t eta)
    · rw [SourceSharpeningSubstitutionProof.listSubstitute]
      exact List.mem_map.mpr ⟨⟨tau,s⟩,hm,rfl⟩
    · exact SourceSharpeningSubstitutionProof.relatedSubstitution Symbol arity Gamma Delta tau s t theta eta hs H
  | whole _ _ _ _ _ _ hs =>
    exact .whole _ _ _ _ tau _
      (SourceSharpeningSubstitutionProof.relatedSubstitution Symbol arity Gamma Delta tau
        (.marked f tau base sourceTypes extras) t theta eta hs H)

theorem extrasSubstitute {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta sourceTypes targetTypes : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (extras : Arguments Symbol arity Gamma sourceTypes) (target : Arguments Symbol arity Gamma targetTypes)
    (h : ExtrasSharp Symbol arity Gamma f base sourceTypes extras target)
    (theta eta : MarkedSubstitution Symbol arity Gamma Delta)
    (H : ∀ tau (v : Variable Gamma tau),Sharp Symbol arity Delta (theta v) (eta v)) :
    ExtrasSharp Symbol arity Delta f (substituteArguments base theta) sourceTypes
      (substituteArguments extras theta) (substituteArguments target eta) := by
  induction targetTypes with
  | nil => cases target; exact .nil _ _ _ _
  | cons tau types ih =>
    cases target with
    | cons q rest =>
      cases h with
      | cons _ _ _ _ _ _ _ _ hq hr =>
        exact .cons _ _ _ _ tau types _ _ (extraSubstitute f base extras q hq theta eta H) (ih rest hr)

theorem appendSourceExtra {Symbol : Type} {arity : Symbol → Nat} {Gamma types moreTypes : List Ty} {tau : Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (extras : Arguments Symbol arity Gamma types) (more : Arguments Symbol arity Gamma moreTypes)
    (t : MarkedTerm Symbol arity Gamma tau) (h : ExtraSharp Symbol arity Gamma f base types extras ⟨tau,t⟩) :
    ExtraSharp Symbol arity Gamma f base (types++moreTypes) (appendArguments extras more) ⟨tau,t⟩ := by
  cases h with
  | existing _ _ _ _ _ s _ hm hs =>
    apply ExtraSharp.existing _ _ _ _ tau s t
    · rw [listAppend]; exact List.mem_append_left _ hm
    · exact hs
  | whole _ _ _ _ _ _ hs =>
    exact .whole _ _ _ _ tau t
      (SourceSharpeningCompositionProof.transitivity Symbol arity Gamma tau _ _ t
        (SourceSharpeningCompositionProof.additionalExtras Symbol arity Gamma f tau base types moreTypes extras more) hs)

theorem appendSourceExtras {Symbol : Type} {arity : Symbol → Nat} {Gamma types moreTypes targetTypes : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (extras : Arguments Symbol arity Gamma types) (more : Arguments Symbol arity Gamma moreTypes)
    (target : Arguments Symbol arity Gamma targetTypes) (h : ExtrasSharp Symbol arity Gamma f base types extras target) :
    ExtrasSharp Symbol arity Gamma f base (types++moreTypes) (appendArguments extras more) target := by
  induction targetTypes with
  | nil => cases target; exact .nil _ _ _ _
  | cons tau types ih =>
    cases target with
    | cons q rest =>
      cases h with
      | cons _ _ _ _ _ _ _ _ hq hr =>
        exact .cons _ _ _ _ tau types q rest (appendSourceExtra f base extras more q hq) (ih rest hr)

theorem appendTargets {Symbol : Type} {arity : Symbol → Nat} {Gamma sourceTypes typesA typesB : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (extras : Arguments Symbol arity Gamma sourceTypes) (a : Arguments Symbol arity Gamma typesA)
    (b : Arguments Symbol arity Gamma typesB) (ha : ExtrasSharp Symbol arity Gamma f base sourceTypes extras a)
    (hb : ExtrasSharp Symbol arity Gamma f base sourceTypes extras b) :
    ExtrasSharp Symbol arity Gamma f base sourceTypes extras (appendArguments a b) := by
  induction typesA with
  | nil => cases a; exact hb
  | cons tau types ih =>
    cases a with
    | cons q rest =>
      cases ha with
      | cons _ _ _ _ _ _ _ _ hq hr =>
        exact .cons _ _ _ _ tau (types++typesB) q (appendArguments rest b) hq (ih rest hr)

theorem appendWhole {Symbol : Type} {arity : Symbol → Nat} {Gamma typesA typesB inputTypes : List Ty}
    (f : Head Symbol) (tau : Ty) (baseA baseB : Arguments Symbol arity Gamma (headArguments arity f))
    (extrasA : Arguments Symbol arity Gamma typesA) (extrasB : Arguments Symbol arity Gamma typesB)
    (argsA argsB : Arguments Symbol arity Gamma inputTypes)
    (hb : ArgumentsSharp Symbol arity Gamma baseA baseB)
    (he : ExtrasSharp Symbol arity Gamma f baseA typesA extrasA extrasB)
    (hi : ArgumentsSharp Symbol arity Gamma argsA argsB) :
    Sharp Symbol arity Gamma (.marked f tau baseA (typesA++inputTypes) (appendArguments extrasA argsA))
      (.marked f tau baseB (typesB++inputTypes) (appendArguments extrasB argsB)) := by
  apply Sharp.marked f tau baseA baseB _ _ _ _ hb
  apply appendTargets
  · exact appendSourceExtras f baseA extrasA argsA extrasB he
  · apply SourceSharpeningReflexivityProof.extrasFromArguments f baseA (appendArguments extrasA argsA) argsA argsB hi
    intro p hp
    rw [listAppend]
    exact List.mem_append_right _ hp

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningApplicationSupportProof
