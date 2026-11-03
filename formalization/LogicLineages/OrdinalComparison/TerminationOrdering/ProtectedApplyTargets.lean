module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedApplyDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedApplyTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open OriginalSpineActions ProtectedPrefix ProtectedApply

def ConsumedBinderEnvironment : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta pre : List Ty) (s : MarkedSubstitution Symbol arity Gamma Delta)
    (consumed : Arguments Symbol arity Delta pre) (sigma : Ty)
    (a : MarkedTerm Symbol arity Delta sigma),
  @Eq (MarkedSubstitution Symbol arity (sigma::(pre++Gamma)) Delta)
    (closeFree s (.cons a consumed)) (extendEnvironment (closeFree s consumed) a)

def EmptyTuple : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma Delta : List Ty)
    (sigma : Ty) (q : MarkedTerm Symbol arity Gamma sigma) (mask : Protected Gamma)
    (s : MarkedSubstitution Symbol arity Gamma Delta),
  applyWith q mask s .nil rfl=some (substituteTerm q s)

/-- Exact prefix-origin correspondence, not arbitrary-mask irrelevance. -/
def LiteralPrefixEquation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta pre : List Ty) (sigma tau : Ty)
    (q : MarkedTerm Symbol arity (pre++Gamma) sigma)
    (s : MarkedSubstitution Symbol arity Gamma Delta)
    (consumed : Arguments Symbol arity Delta pre) (types : List Ty)
    (args : Arguments Symbol arity Delta types) (h : sigma=arrows types tau),
  applyWith q (mask pre Gamma) (closeFree s consumed) args h=
    applyFrame q s consumed args h

def InitialOriginalEquation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (sigma tau : Ty) (q : MarkedTerm Symbol arity Gamma sigma)
    (s : MarkedSubstitution Symbol arity Gamma Delta) (types : List Ty)
    (args : Arguments Symbol arity Delta types) (h : sigma=arrows types tau),
  applyWith q (fun _ => false) s args h=
    applyOriginalWith (substituteTerm q s) (fun v => .var v) args h

end LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedApplyTargets
