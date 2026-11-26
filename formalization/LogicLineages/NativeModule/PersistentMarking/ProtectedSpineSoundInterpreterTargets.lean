module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineSoundStageTargets
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineLawTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundInterpreterTargets
open Spine DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineSoundRelation ProtectedSpineSoundStageTargets
open ProtectedSpineEnvironment ProtectedSpineInterpreter ProtectedSpineLaws

def Frame (F : Inputs S) (Γ : Context) (types : List Ty) (values : Args) (bound : BoundValues) : Prop :=
  BaseTyped EmptyContext values types ∧ Sources F Γ values ∧ BaseRelated F Γ bound values

def TupleRelated (F : Inputs S) (Γ : Context) (ds : List Ty) (xs : List Code) (args : Args) : Prop :=
  ∀ i ρ x a, ds[i]? = some ρ → xs[i]? = some x → At args i a → Related F ρ Γ x (some a)

def ExprGoal (F : Inputs S) (M : Code) (q : Expr) : Prop :=
  ∀ Γ types values cs,
  Typed (BoundContext.prefix types EmptyContext) q q.type →
  Source F Γ q → WellFormed F.data.types F.data.ports Γ → Frame F Γ types values cs →
  Related F q.type Γ (codeAt (domain F) q.type (evaluate S (domain F) F.data.sourceHeads M q) Γ ⟨[],cs⟩)
    (some (substitute values 0 q)) ∧
  ∀ consumed outer, values = consumed.append outer → ∀ ds τ xs args,
    (ds,τ) ∈ fullPrefixes q.type → TupleValues (domain F) Γ ds xs →
    CallTyped EmptyContext q.type args τ → Sources F Γ args → TupleRelated F Γ ds xs args →
    Related F τ Γ (nonemptyAt (domain F) (evaluate S (domain F) F.data.sourceHeads M q) Γ ⟨[],cs⟩
      consumed.length ds τ xs)
      (applyAux (substitute outer consumed.length q) args consumed)

def ArgsGoal (F : Inputs S) (M : Code) (qs : Args) : Prop :=
  ∀ Γ types values cs,
  ExtrasTyped (BoundContext.prefix types EmptyContext) qs →
  Sources F Γ qs → WellFormed F.data.types F.data.ports Γ → Frame F Γ types values cs →
  BaseRelated F Γ (evaluateArgs S (domain F) F.data.sourceHeads M qs Γ [] cs) (substituteArgs values 0 qs)

def InterpreterSound : Prop := ∀ S (F : Inputs S) M,
  M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads →
  FamilyRelated F M → ∀ q, ExprGoal F M q

end LogicLineages.PersistentMarking.ProtectedSpineSoundInterpreterTargets
