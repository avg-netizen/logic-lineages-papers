module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedEliminationTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedRefinementProof
open Source Source.SourceMarkedSyntax RecursiveComparison SourceSharpening SourceUnmarked SourceExtendedElimination

theorem unpack {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    {q : Packed Symbol arity Gamma} {s : MarkedTerm Symbol arity Gamma tau}
    (h : Refines Symbol arity Gamma q ⟨tau,s⟩) :
    ∃ src : MarkedTerm Symbol arity Gamma tau,q=⟨tau,src⟩ ∧ Sharp Symbol arity Gamma src s := by
  cases h with
  | mk q s hs => exact ⟨q,rfl,hs⟩

theorem reflexive {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (p : Packed Symbol arity Gamma) : Refines Symbol arity Gamma p p := by
  cases p with
  | mk tau q => exact .mk q q (SourceSharpeningReflexivityProof.reflexiveTerm q)

theorem transitive {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    {p q s : Packed Symbol arity Gamma} (hpq : Refines Symbol arity Gamma p q)
    (hqs : Refines Symbol arity Gamma q s) : Refines Symbol arity Gamma p s := by
  cases hpq with
  | mk p q hpq =>
    cases hqs with
    | mk q s hqs => exact .mk p s (SourceSharpeningCompositionProof.transitivity Symbol arity Gamma _ p q s hpq hqs)

theorem argumentsRefinement {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (qs ss : Arguments Symbol arity Gamma types) (h : ArgumentsSharp Symbol arity Gamma qs ss) :
    List.Forall₂ (Refines Symbol arity Gamma) (argumentList qs) (argumentList ss) := by
  induction types with
  | nil => cases qs; cases ss; exact .nil
  | cons tau types ih =>
    cases h with
    | cons q s qs ss hq hr => exact .cons (.mk q s hq) (ih qs ss hr)

theorem memberRight {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    {qs ss : List (Packed Symbol arity Gamma)} (h : List.Forall₂ (Refines Symbol arity Gamma) qs ss) :
    ∀ s∈ss,∃ q∈qs,Refines Symbol arity Gamma q s := by
  induction h with
  | nil => simp
  | @cons q s qs ss hq hr ih =>
    intro x hx
    rcases List.mem_cons.mp hx with he | hm
    · subst x; exact ⟨q,List.mem_cons_self ..,hq⟩
    · obtain ⟨r,hr,href⟩ := ih x hm
      exact ⟨r,List.mem_cons_of_mem _ hr,href⟩

theorem argumentMember {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty} {tau : Ty}
    (qs ss : Arguments Symbol arity Gamma types) (h : ArgumentsSharp Symbol arity Gamma qs ss)
    (s : MarkedTerm Symbol arity Gamma tau) (hs : (⟨tau,s⟩ : Packed Symbol arity Gamma)∈argumentList ss) :
    ∃ q : MarkedTerm Symbol arity Gamma tau,(⟨tau,q⟩ : Packed Symbol arity Gamma)∈argumentList qs ∧
      Sharp Symbol arity Gamma q s := by
  obtain ⟨p,hp,href⟩ := memberRight (argumentsRefinement qs ss h) ⟨tau,s⟩ hs
  obtain ⟨q,he,hsharp⟩ := unpack href
  exact ⟨q,he ▸ hp,hsharp⟩

theorem allArguments {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (args : Arguments Symbol arity Gamma types) (h : ArgumentsUnmarked Symbol arity Gamma args) :
    AllUnmarked (argumentList args) := by
  induction types with
  | nil => cases args; intro p hp; cases hp
  | cons tau types ih =>
    cases h with
    | cons q rest hq hr =>
      intro p hp
      rcases List.mem_cons.mp hp with he | hm
      · subst p; exact hq
      · exact ih rest hr p hm

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedRefinementProof
