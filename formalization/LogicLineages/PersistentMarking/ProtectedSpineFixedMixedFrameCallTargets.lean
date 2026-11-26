import LogicLineages.PersistentMarking.ProtectedSpineFixedSimultaneousFreeAllCallTargets

namespace LogicLineages.PersistentMarking.ProtectedSpineFixedMixedFrameCallTargets
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineInterpreter
open ProtectedSpineSubstitutionTargets ProtectedSpineBoundTargets ProtectedSpineFixedApplicationTargets
open MarkedConstructorTargets (PrefixClosed)
open MarkedConstructorOperator (step)

/-- The original helper at a consumed literal binder prefix, with a
separate actual free-image environment. Its argument tuple is typed
outside those consumed binders. -/
def helperWithFree (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (Γ : Context) (q : Expr) (args consumed : Args) (a : FreeValues) (τ : Ty) : Code :=
  let frame : Assignments := ⟨a,closedCodes S E H M Γ consumed⟩
  match args with
  | .nil => codeAt E τ (evaluate S E H M q) Γ frame
  | .cons _ _ => nonemptyAt E (evaluate S E H M q) Γ frame consumed.length
      (domainTypes args) τ ((evaluateArgs S E H M args Γ a []).map Prod.snd)

/-- Simultaneous free substitution into the source and original tuple
commutes with its fixed-point whole call at an arbitrary typed
consumed bound prefix. The consumed images are already concrete in
the resulting environment; coverage and actual typing are explicit. -/
def FixedMixedFrameCall : Prop :=
  ∀ (S : Signature) (E : Environment) (H : List Head) (M : Code) (Γ : Context)
    (θ : FreeMap) (q : Expr) (xs consumed : Args) (types : List Ty) (τ : Ty) (a : FreeValues),
    let ys := freeSubArgs θ 0 xs
    PrefixClosed E → M ∈ MarkedFamilyCoherence.retained E H → step S E H M = M →
    FreeImages E H θ → BoundImages E H consumed types →
    Typed (BoundContext.prefix types EmptyContext) q q.type →
    Covered E H q → Covered E H (freeSub θ 0 q) →
    CallTyped EmptyContext q.type xs τ → ArgsCovered E H xs → ArgsCovered E H ys →
    InputValid E Γ ⟨a,[]⟩ →
    FreeSubstitutionInputs S E H M θ Γ ⟨a,[]⟩ ⟨[],[]⟩ →
    helperWithFree S E H M Γ q xs consumed a τ =
      concreteOutput S E H M Γ τ (applyAux (freeSub θ 0 q) ys consumed)

end LogicLineages.PersistentMarking.ProtectedSpineFixedMixedFrameCallTargets
