module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalTargetUnmarkedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceUnmarkedProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinarySyntaxCoverage
open Source Source.SourceMarkedSyntax RecursiveComparison

inductive OrdinaryArguments (Symbol : Type) (arity : Symbol → Nat) : List Ty → List Ty → Type where
  | nil {Gamma} : OrdinaryArguments Symbol arity Gamma []
  | cons {Gamma sigma types} (q : Term Symbol arity Gamma sigma) (rest : OrdinaryArguments Symbol arity Gamma types) :
      OrdinaryArguments Symbol arity Gamma (sigma::types)

def embedArguments {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty} :
    OrdinaryArguments Symbol arity Gamma types → Arguments Symbol arity Gamma types
  | .nil => .nil
  | .cons q rest => .cons (embed q) (embedArguments rest)

def groundAt {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} :
    (n : Nat) → OrdinaryArguments Symbol arity Gamma (List.replicate n .ground) → Fin n → Term Symbol arity Gamma .ground
  | 0,_,i => Fin.elim0 i
  | n+1,.cons q rest,i => Fin.cases q (groundAt n rest) i

def buildTerm {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} :
    (f : Head Symbol) → OrdinaryArguments Symbol arity Gamma (headArguments arity f) → Term Symbol arity Gamma (headResult f)
  | .zero,.nil => .zeroC
  | .succ,.nil => .succC
  | .cases tau,.nil => .caseC tau
  | .recursor tau,.nil => .recC tau
  | .application sigma tau,.cons f (.cons a .nil) => .app f a
  | .ranked s,args => .ranked s (groundAt (arity s) args)

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinarySyntaxCoverage
