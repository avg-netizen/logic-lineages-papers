module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveComparisonDefinitions
public import LogicLineages.OrdinalComparison.SourceMarkedBindingDefinitions

@[expose] public section
/-! Literal typed bottom-free/no-meta fragment of Kop (2012), proof of
Lemma5.25, printed122–124, auxiliary relation ] (here `Sharp`).
https://www.cs.ru.nl/~cynthiakop/phdthesis.pdf
This is an auxiliary SYNTAX relation, not a replacement for Original Weak,
its transitive closure, or a supplied reduction-pair theorem. -/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpening
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding RecursiveComparison

mutual
inductive Sharp (Symbol : Type) (arity : Symbol → Nat) :
    (Gamma : List Ty) →
    {tau : Ty} → MarkedTerm Symbol arity Gamma tau → MarkedTerm Symbol arity Gamma tau → Prop where
  | var {Gamma : List Ty} {tau : Ty} (v : Variable Gamma tau) : Sharp Symbol arity Gamma (.var v) (.var v)
  | lam {Gamma : List Ty} {sigma tau : Ty} (s t : MarkedTerm Symbol arity (sigma::Gamma) tau) :
      Sharp Symbol arity (sigma::Gamma) s t → Sharp Symbol arity Gamma (.lam s) (.lam t)
  | ordinary {Gamma : List Ty} (f : Head Symbol) (ss ts : Arguments Symbol arity Gamma (headArguments arity f)) :
      ArgumentsSharp Symbol arity Gamma ss ts → Sharp Symbol arity Gamma (.ordinary f ss) (.ordinary f ts)
  | marked {Gamma : List Ty} (f : Head Symbol) (tau : Ty) (ss ts : Arguments Symbol arity Gamma (headArguments arity f))
      (sourceTypes : List Ty) (sourceExtras : Arguments Symbol arity Gamma sourceTypes)
      (targetTypes : List Ty) (targetExtras : Arguments Symbol arity Gamma targetTypes) :
      ArgumentsSharp Symbol arity Gamma ss ts →
      ExtrasSharp Symbol arity Gamma f ss sourceTypes sourceExtras targetExtras →
      Sharp Symbol arity Gamma (.marked f tau ss sourceTypes sourceExtras) (.marked f tau ts targetTypes targetExtras)
inductive ArgumentsSharp (Symbol : Type) (arity : Symbol → Nat) :
    (Gamma : List Ty) →
    {types : List Ty} → Arguments Symbol arity Gamma types → Arguments Symbol arity Gamma types → Prop where
  | nil {Gamma : List Ty} : ArgumentsSharp Symbol arity Gamma .nil .nil
  | cons {Gamma : List Ty} {sigma : Ty} {types : List Ty} (s t : MarkedTerm Symbol arity Gamma sigma)
      (ss ts : Arguments Symbol arity Gamma types) :
      Sharp Symbol arity Gamma s t → ArgumentsSharp Symbol arity Gamma ss ts →
      ArgumentsSharp Symbol arity Gamma (.cons s ss) (.cons t ts)
inductive ExtraSharp (Symbol : Type) (arity : Symbol → Nat) :
    (Gamma : List Ty) →
    (f : Head Symbol) → Arguments Symbol arity Gamma (headArguments arity f) →
    (sourceTypes : List Ty) → Arguments Symbol arity Gamma sourceTypes → Packed Symbol arity Gamma → Prop where
  | existing {Gamma : List Ty} (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
      (sourceTypes : List Ty) (sourceExtras : Arguments Symbol arity Gamma sourceTypes)
      (tau : Ty) (s t : MarkedTerm Symbol arity Gamma tau) :
      (⟨tau,s⟩ : Packed Symbol arity Gamma)∈argumentList sourceExtras → Sharp Symbol arity Gamma s t →
      ExtraSharp Symbol arity Gamma f base sourceTypes sourceExtras ⟨tau,t⟩
  | whole {Gamma : List Ty} (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
      (sourceTypes : List Ty) (sourceExtras : Arguments Symbol arity Gamma sourceTypes)
      (tau : Ty) (t : MarkedTerm Symbol arity Gamma tau) :
      Sharp Symbol arity Gamma (.marked f tau base sourceTypes sourceExtras) t →
      ExtraSharp Symbol arity Gamma f base sourceTypes sourceExtras ⟨tau,t⟩
inductive ExtrasSharp (Symbol : Type) (arity : Symbol → Nat) :
    (Gamma : List Ty) →
    (f : Head Symbol) → Arguments Symbol arity Gamma (headArguments arity f) →
    (sourceTypes : List Ty) → Arguments Symbol arity Gamma sourceTypes →
    {targetTypes : List Ty} → Arguments Symbol arity Gamma targetTypes → Prop where
  | nil {Gamma : List Ty} (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
      (sourceTypes : List Ty) (sourceExtras : Arguments Symbol arity Gamma sourceTypes) :
      ExtrasSharp Symbol arity Gamma f base sourceTypes sourceExtras .nil
  | cons {Gamma : List Ty} (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
      (sourceTypes : List Ty) (sourceExtras : Arguments Symbol arity Gamma sourceTypes)
      (tau : Ty) (types : List Ty) (t : MarkedTerm Symbol arity Gamma tau) (ts : Arguments Symbol arity Gamma types) :
      ExtraSharp Symbol arity Gamma f base sourceTypes sourceExtras ⟨tau,t⟩ →
      ExtrasSharp Symbol arity Gamma f base sourceTypes sourceExtras ts →
      ExtrasSharp Symbol arity Gamma f base sourceTypes sourceExtras (.cons t ts)
end

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpening
