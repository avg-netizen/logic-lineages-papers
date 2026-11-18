import LogicLineages.PersistentMarking.ProtectedSpineBoundTargets
import LogicLineages.PersistentMarking.MarkedConstructorOperator

namespace LogicLineages.PersistentMarking.ProtectedSpineFixedApplicationTargets
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode
open ProtectedSpineLaws ProtectedSpineInterpreter ProtectedSpineBoundTargets
open MarkedConstructorOperator (step)

def closedCodes (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (Γ : Context) (args : Args) : ProtectedSpineEnvironment.BoundValues :=
  evaluateArgs S E H M args Γ [] []

def domainTypes (args : Args) : List Ty := (MarkedConstructorTests.terms args).map Expr.type

def concreteOutput (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (Γ : Context) (τ : Ty) (r : Option Expr) : Code :=
  match r with
  | none => StructuralActions.bottom E τ Γ
  | some q => codeAt E τ (evaluate S E H M q) Γ ⟨[],[]⟩

def helperAux (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (Γ : Context) (q : Expr) (args values : Args) (τ : Ty) : Code :=
  let a : Assignments := ⟨[],closedCodes S E H M Γ values⟩
  match args with
  | .nil => codeAt E τ (evaluate S E H M q) Γ a
  | .cons _ _ => nonemptyAt E (evaluate S E H M q) Γ a values.length
      (domainTypes args) τ ((closedCodes S E H M Γ args).map Prod.snd)

def FixedApplicationAux : Prop := ∀ S E H M Γ q args values types τ,
  MarkedConstructorTargets.PrefixClosed E → M ∈ MarkedFamilyCoherence.retained E H → step S E H M = M →
  WellFormed E.types E.ports Γ → BoundImages E H values types →
  Typed (BoundContext.prefix types EmptyContext) q q.type → Covered E H q →
  CallTyped EmptyContext q.type args τ → ArgsCovered E H args →
  helperAux S E H M Γ q args values τ = concreteOutput S E H M Γ τ (applyAux q args values)

def FixedApplication : Prop := ∀ S E H M Γ q args τ,
  MarkedConstructorTargets.PrefixClosed E → M ∈ MarkedFamilyCoherence.retained E H → step S E H M = M →
  WellFormed E.types E.ports Γ → Typed EmptyContext q q.type → Covered E H q →
  CallTyped EmptyContext q.type args τ → ArgsCovered E H args →
  call S E H M q Γ [] [] (domainTypes args) ((closedCodes S E H M Γ args).map Prod.snd) τ =
    concreteOutput S E H M Γ τ (apply q args)

end LogicLineages.PersistentMarking.ProtectedSpineFixedApplicationTargets
