module
public import LogicLineages.OrdinalComparison.SourceMarkedSyntaxDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceUnmarked
open Source Source.SourceMarkedSyntax

mutual
inductive Unmarked (Symbol : Type) (arity : Symbol → Nat) :
    (Gamma : List Ty) → {tau : Ty} → MarkedTerm Symbol arity Gamma tau → Prop where
  | var {Gamma tau} (v : Variable Gamma tau) : Unmarked Symbol arity Gamma (.var v)
  | lam {Gamma sigma tau} (body : MarkedTerm Symbol arity (sigma::Gamma) tau) :
      Unmarked Symbol arity (sigma::Gamma) body → Unmarked Symbol arity Gamma (.lam body)
  | ordinary {Gamma} (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f)) :
      ArgumentsUnmarked Symbol arity Gamma base → Unmarked Symbol arity Gamma (.ordinary f base)
inductive ArgumentsUnmarked (Symbol : Type) (arity : Symbol → Nat) :
    (Gamma : List Ty) → {types : List Ty} → Arguments Symbol arity Gamma types → Prop where
  | nil {Gamma} : ArgumentsUnmarked Symbol arity Gamma .nil
  | cons {Gamma sigma types} (q : MarkedTerm Symbol arity Gamma sigma) (rest : Arguments Symbol arity Gamma types) :
      Unmarked Symbol arity Gamma q → ArgumentsUnmarked Symbol arity Gamma rest →
      ArgumentsUnmarked Symbol arity Gamma (.cons q rest)
end

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceUnmarked
