module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinarySubstitutionStabilityDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinarySubstitutionStabilityTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison OrdinarySubstitutionStability

def SuccessfulOriginalApply : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (sigma tau : Ty) (types : List Ty)
    (q : MarkedTerm Symbol arity Gamma sigma) (args : Arguments Symbol arity Gamma types)
    (h : sigma=arrows types tau) (r : MarkedTerm Symbol arity Gamma tau)
    (theta : MarkedSubstitution Symbol arity Gamma Delta),
  applyOriginalWith q (fun v => .var v) args h=some r →
    applyOriginalWith (substituteTerm q theta) (fun v => .var v) (substituteArguments args theta) h=
      some (substituteTerm r theta)

/-- Full actual relation stability under ordinary typed substitution, including
all auxiliary marked/retyped intermediates and all three matching relations.
No inductive-step callback, supplied preservation predicate or semantic-family
premise is present. Ordinary image reflexivity is to be PROVED, not assumed. -/
def ActualJointStability : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (above : Symbol → Symbol → Prop),
  (∀ Gamma (s t : Packed Symbol arity Gamma), Weak Symbol arity above Gamma s t →
    ∀ Delta (theta : Substitution Symbol arity Gamma Delta),
      Weak Symbol arity above Delta (substitutePacked theta s) (substitutePacked theta t)) ∧
  (∀ Gamma (s t : Packed Symbol arity Gamma), Strict Symbol arity above Gamma s t →
    ∀ Delta (theta : Substitution Symbol arity Gamma Delta),
      Strict Symbol arity above Delta (substitutePacked theta s) (substitutePacked theta t)) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)), WeakMatch Symbol arity above Gamma ss ts →
    ∀ Delta (theta : Substitution Symbol arity Gamma Delta),
      WeakMatch Symbol arity above Delta (ss.map (substitutePacked theta)) (ts.map (substitutePacked theta))) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)), StrictMultiset Symbol arity above Gamma ss ts →
    ∀ Delta (theta : Substitution Symbol arity Gamma Delta),
      StrictMultiset Symbol arity above Delta (ss.map (substitutePacked theta)) (ts.map (substitutePacked theta))) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)), ReplacementMatch Symbol arity above Gamma ss ts →
    ∀ Delta (theta : Substitution Symbol arity Gamma Delta),
      ReplacementMatch Symbol arity above Delta (ss.map (substitutePacked theta)) (ts.map (substitutePacked theta)))

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinarySubstitutionStabilityTargets
