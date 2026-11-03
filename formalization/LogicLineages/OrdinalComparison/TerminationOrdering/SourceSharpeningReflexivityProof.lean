module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningReflexivityProof
open Source Source.SourceMarkedSyntax RecursiveComparison SourceSharpening

theorem extrasFromArguments {Symbol : Type} {arity : Symbol → Nat} {Gamma sourceTypes types : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (sourceExtras : Arguments Symbol arity Gamma sourceTypes)
    (ss ts : Arguments Symbol arity Gamma types) (h : ArgumentsSharp Symbol arity Gamma ss ts)
    (hin : ∀ p∈argumentList ss,p∈argumentList sourceExtras) :
    ExtrasSharp Symbol arity Gamma f base sourceTypes sourceExtras ts := by
  induction types with
  | nil => cases ts; exact .nil f base sourceTypes sourceExtras
  | cons sigma types ih =>
    cases h with
    | cons s t ss ts hs hr =>
      apply ExtrasSharp.cons f base sourceTypes sourceExtras sigma types t ts
      · exact .existing f base sourceTypes sourceExtras sigma s t
          (hin _ (List.mem_cons_self ..)) hs
      · exact ih ss ts hr (fun p hp => hin p (List.mem_cons_of_mem _ hp))

theorem reflexiveTerm {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : MarkedTerm Symbol arity Gamma tau) : Sharp Symbol arity Gamma q q := by
  induction q using MarkedTerm.rec
    (motive_2 := fun Gamma types args => ArgumentsSharp Symbol arity Gamma args args) with
  | var v => exact .var v
  | lam body ih => exact .lam body body ih
  | ordinary f base ih => exact .ordinary f base base ih
  | marked f tau base types extras ihb ihe =>
    exact .marked f tau base base types extras types extras ihb
      (extrasFromArguments f base extras extras extras ihe (fun p hp => hp))
  | nil => exact .nil
  | cons q rest ihq ihr => exact .cons q q rest rest ihq ihr

theorem reflexiveArguments {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (args : Arguments Symbol arity Gamma types) : ArgumentsSharp Symbol arity Gamma args args := by
  induction types with
  | nil => cases args; exact .nil
  | cons tau types ih =>
    cases args with
    | cons q rest => exact .cons q q rest rest (reflexiveTerm q) (ih rest)

theorem reflexivity : SourceSharpeningTargets.Reflexivity := by
  intro Symbol arity Gamma
  exact ⟨fun _ q => reflexiveTerm q,fun _ args => reflexiveArguments args⟩

theorem retagging : SourceSharpeningTargets.Retagging := by
  intro Symbol arity Gamma f sigma tau baseS baseT typesS typesT extrasS extrasT h
  cases h with
  | marked f sigma baseS baseT typesS extrasS typesT extrasT hb he =>
    exact .marked f tau baseS baseT typesS extrasS typesT extrasT hb he

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningReflexivityProof
