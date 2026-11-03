module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedApplyBindingProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SuccessfulApplicationSubstitutionTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison

/-- Post-substitution in the ACTUAL successful original-spine helper. Original
source syntax is retained, and all output substitutions/tuple images are literal. -/
def PostSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta Xi : List Ty) (sigma tau : Ty) (types : List Ty)
    (q : MarkedTerm Symbol arity Gamma sigma) (env : MarkedSubstitution Symbol arity Gamma Delta)
    (args : Arguments Symbol arity Delta types) (h : sigma=arrows types tau)
    (r : MarkedTerm Symbol arity Delta tau) (post : MarkedSubstitution Symbol arity Delta Xi),
  applyOriginalWith q env args h=some r →
  applyOriginalWith q (fun v => substituteTerm (env v) post) (substituteArguments args post) h=
    some (substituteTerm r post)

/-- Substituting the SOURCE can unlock a previously blocked variable. Only
SUCCESS preservation is claimed: no equality of arbitrary Option results or
failure reflection, arbitrary mask irrelevance, or unary currying is asserted. -/
def SourceSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta Xi : List Ty) (sigma tau : Ty) (types : List Ty)
    (q : MarkedTerm Symbol arity Gamma sigma) (theta : MarkedSubstitution Symbol arity Gamma Delta)
    (env : MarkedSubstitution Symbol arity Delta Xi) (args : Arguments Symbol arity Xi types)
    (h : sigma=arrows types tau) (r : MarkedTerm Symbol arity Xi tau),
  applyOriginalWith q (fun v => substituteTerm (theta v) env) args h=some r →
  applyOriginalWith (substituteTerm q theta) env args h=some r

def StrictMarkSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (tau : Ty) (q r : MarkedTerm Symbol arity Gamma tau)
    (theta : MarkedSubstitution Symbol arity Gamma Delta),
  strictMark q=some r → strictMark (substituteTerm q theta)=some (substituteTerm r theta)

end LogicLineages.OrdinalComparison.TerminationOrdering.SuccessfulApplicationSubstitutionTargets
