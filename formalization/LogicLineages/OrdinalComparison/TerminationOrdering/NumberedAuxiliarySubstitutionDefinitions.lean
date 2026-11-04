module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryShiftProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectCertificateDefinitions

@[expose] public section
/-! Literal finite substitution environments and capture-avoiding code substitution.
Lifting an environment inserts the new bound variable and weakens every old
replacement with the checked numeric weakening. The beta consumer is exactly
the existing directTarget beta rule, not original functional-head application.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliarySubstitution
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryShift

def liftEnvironment {Symbol : Type} (environment : List (Code Symbol)) : List (Code Symbol) :=
  .var 0 :: environment.map (shiftCode 0)

def substituteCode {Symbol : Type} (environment : List (Code Symbol)) : Code Symbol → Code Symbol
  | .var index => environment[index]?.getD (.var index)
  | .lam sigma body => .lam sigma (substituteCode (liftEnvironment environment) body)
  | .app sigma q a => .app sigma (substituteCode environment q) (substituteCode environment a)
  | .bottom tau => .bottom tau
  | .ordinary head base => .ordinary head (substituteCode environment base)
  | .numbered k head tau base types extras =>
      .numbered k head tau (substituteCode environment base) types (substituteCode environment extras)
  | .argumentsNil => .argumentsNil
  | .argumentsCons sigma q rest =>
      .argumentsCons sigma (substituteCode environment q) (substituteCode environment rest)

def substitutionCodes {Symbol : Type} {arity : Symbol → Nat} {Delta : List Ty} :
    (Gamma : List Ty) → NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta → List (Code Symbol)
  | [],_ => []
  | _::Gamma,rho => termCode (rho .here) :: substitutionCodes Gamma (fun v => rho (.there v))

def betaCode {Symbol : Type} (free : Nat) : Code Symbol → Option (Code Symbol)
  | .app _ (.lam _ body) argument =>
      some (substituteCode (argument :: (List.range free).map Code.var) body)
  | _ => none

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliarySubstitution
