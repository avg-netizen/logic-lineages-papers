module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowApplicationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowAngleTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication NumberedRewriteSyntax NumberedRewriteReduction NumberedOriginalAngle NumberedFiniteUniverse NumberedUniverseBindingTargets NumberedWindowTraces

def ActualGeneralOriginalAngle : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (n : Nat) (Gamma Delta : List Ty) (sigma : Ty)
    (q : MarkedTerm Symbol arity Gamma sigma) (env : MarkedSubstitution Symbol arity Gamma Delta)
    (types : List Ty) (tau : Ty) (args : Arguments Symbol arity Delta types) (suffix : sigma=arrows types tau)
    (r : MarkedTerm Symbol arity Delta tau),applyOriginalWith q env args suffix=some r →
    ∀ (Q : AuxTerm Symbol arity Delta sigma) (values : AuxArguments Symbol arity Delta types),
    Represents Symbol arity (n+types.length) Delta sigma (substituteTerm q env) Q →
    ArgumentsRepresent Symbol arity (n+types.length) Delta types args values →
    ∃ (R : AuxTerm Symbol arity Delta tau) (m : Nat),WindowTypedTrace Symbol arity symbols S above Delta tau m
      (applyArguments (transportAux suffix Q) values) R ∧ Represents Symbol arity n Delta tau r R

def ActualSpecialApplication : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (n : Nat) (Gamma types : List Ty) (tau : Ty)
    (q : MarkedTerm Symbol arity Gamma (arrows types tau)) (args : Arguments Symbol arity Gamma types)
    (r : MarkedTerm Symbol arity Gamma tau),specialApply q args=some r →
    ∀ (Q : AuxTerm Symbol arity Gamma (arrows types tau)) (values : AuxArguments Symbol arity Gamma types),
    Represents Symbol arity (n+types.length) Gamma (arrows types tau) q Q →
    ArgumentsRepresent Symbol arity (n+types.length) Gamma types args values →
    ∃ (R : AuxTerm Symbol arity Gamma tau) (m : Nat),WindowTypedTrace Symbol arity symbols S above Gamma tau m
      (applyArguments Q values) R ∧ Represents Symbol arity n Gamma tau r R

def ActualOrdinaryAngleTranslation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (n : Nat) (Gamma : List Ty) (sigma : Ty)
    (q : Term Symbol arity Gamma sigma) (types : List Ty) (tau : Ty)
    (args : Arguments Symbol arity Gamma types) (suffix : sigma=arrows types tau)
    (r : MarkedTerm Symbol arity Gamma tau),applyOriginalWith (embed q) (fun v => .var v) args suffix=some r →
    ∃ (R : AuxTerm Symbol arity Gamma tau) (m : Nat),WindowTypedTrace Symbol arity symbols S above Gamma tau m
      (applyArguments (transportAux suffix (translateOriginal q)) (canonicalArguments (n+types.length) args)) R ∧
      Represents Symbol arity n Gamma tau r R

def ActualConfinedSpecialApplication : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty),
    SubtypeClosed (fun t => t∈S) → ∀ (above : Symbol → Symbol → Prop) (n : Nat) (Gamma types : List Ty) (tau : Ty)
    (q : MarkedTerm Symbol arity Gamma (arrows types tau)) (args : Arguments Symbol arity Gamma types)
    (r : MarkedTerm Symbol arity Gamma tau),specialApply q args=some r →
    ∀ (Q : AuxTerm Symbol arity Gamma (arrows types tau)) (values : AuxArguments Symbol arity Gamma types),
    Represents Symbol arity (n+types.length) Gamma (arrows types tau) q Q →
    ArgumentsRepresent Symbol arity (n+types.length) Gamma types args values →
    InUniverse symbols S Q → GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) values →
    ∃ (R : AuxTerm Symbol arity Gamma tau) (m : Nat)
      (path : WindowTypedTrace Symbol arity symbols S above Gamma tau m (applyArguments Q values) R),
      Represents Symbol arity n Gamma tau r R ∧ allBoundaries (NumberedWindowTracesProof.typedToPacked path)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowAngleTargets
