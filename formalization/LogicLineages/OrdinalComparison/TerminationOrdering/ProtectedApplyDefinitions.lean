module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedPrefixProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedApply
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open OriginalSpineActions ProtectedPrefix

/-- Generalized original-spine SYNTAX scanner. Protection is substantive:
a protected source variable blocks a nonempty tuple BEFORE substitution;
an old free variable applies its complete substituted source simultaneously.
The following targets pay its exact literal-prefix/original-source meaning. -/
def applyWith {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {sigma : Ty}
    (q : MarkedTerm Symbol arity Gamma sigma) :
    {Delta : List Ty} → Protected Gamma →
    {types : List Ty} → {tau : Ty} →
    MarkedSubstitution Symbol arity Gamma Delta → Arguments Symbol arity Delta types →
    sigma=arrows types tau → Option (MarkedTerm Symbol arity Delta tau) :=
  fun {Delta} mask {types} {tau} s args => match q with
  | .var v => match args with
    | .nil => fun h => some (transportTerm h (s v))
    | .cons a rest => fun h =>
      if mask v then none else applyOriginalWith (s v) (fun w => .var w) (.cons a rest) h
  | .lam body => match args with
    | .nil => fun h => some (transportTerm h (substituteTerm (.lam body) s))
    | .cons a rest => fun h =>
      applyWith body (LambdaSpineActions.protectExtend mask)
        (extendEnvironment s (transportTerm (Ty.arrow.inj h).1.symm a)) rest (Ty.arrow.inj h).2
  | .ordinary f base => fun h => applyOriginalWith (.ordinary f base) s args h
  | .marked f out base extraTypes extras => fun h =>
      applyOriginalWith (.marked f out base extraTypes extras) s args h

def closeFree {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta pre : List Ty}
    (s : MarkedSubstitution Symbol arity Gamma Delta) (consumed : Arguments Symbol arity Delta pre) :
    MarkedSubstitution Symbol arity (pre++Gamma) Delta :=
  fun v => substituteTerm (liftFree pre s v) (closePrefix consumed)

end LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedApply
