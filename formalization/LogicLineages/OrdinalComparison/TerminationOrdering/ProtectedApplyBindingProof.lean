module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedApplyTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedApplyBindingProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open OriginalSpineActions ProtectedPrefix ProtectedApply

variable {Symbol : Type} {arity : Symbol → Nat}

theorem substitutionComposition {Gamma : List Ty} {tau : Ty} (q : MarkedTerm Symbol arity Gamma tau) :
    ∀ (Delta Xi : List Ty) (s : MarkedSubstitution Symbol arity Gamma Delta)
      (r : MarkedSubstitution Symbol arity Delta Xi),
      substituteTerm (substituteTerm q s) r=substituteTerm q (fun v => substituteTerm (s v) r) := by
  induction q using MarkedTerm.rec
    (motive_2 := fun Gamma types args => ∀ (Delta Xi : List Ty)
      (s : MarkedSubstitution Symbol arity Gamma Delta) (r : MarkedSubstitution Symbol arity Delta Xi),
      substituteArguments (substituteArguments args s) r=
        substituteArguments args (fun v => substituteTerm (s v) r)) with
  | var v => intros; rfl
  | @lam Omega sigma upsilon body ih =>
    intro Delta Xi s r
    apply congrArg MarkedTerm.lam
    rw [ih]
    apply congrArg (substituteTerm body)
    funext tau v
    cases v with
    | here => rfl
    | there v =>
      exact RenamingEquivarianceBindingProof.substitutionCovariance Symbol arity Delta (sigma::Delta) Xi (sigma::Xi)
        _ (s v) (Renaming.weaken Delta sigma) (Renaming.weaken Xi sigma) r (liftSubstitution r)
        (by intros; rfl)
  | ordinary f base ih =>
    intro Delta Xi s r
    exact congrArg (MarkedTerm.ordinary f) (ih Delta Xi s r)
  | marked f out base types extras ihb ihe =>
    intro Delta Xi s r
    exact congrArg₂ (fun b e => MarkedTerm.marked f out b types e) (ihb Delta Xi s r) (ihe Delta Xi s r)
  | nil => intros; rfl
  | cons q rest ihq ihr =>
    rename_i Delta Xi s r
    exact congrArg₂ Arguments.cons (ihq Delta Xi s r) (ihr Delta Xi s r)

theorem argumentsComposition {Gamma Delta Xi types : List Ty}
    (args : Arguments Symbol arity Gamma types) (s : MarkedSubstitution Symbol arity Gamma Delta)
    (r : MarkedSubstitution Symbol arity Delta Xi) :
    substituteArguments (substituteArguments args s) r=
      substituteArguments args (fun v => substituteTerm (s v) r) := by
  induction types with
  | nil => cases args; rfl
  | cons tau types ih =>
    cases args with
    | cons q rest => exact congrArg₂ Arguments.cons (substitutionComposition q Delta Xi s r) (ih rest)

theorem dropClosing {Gamma Delta : List Ty} {sigma tau : Ty}
    (q : MarkedTerm Symbol arity Gamma tau) (s : MarkedSubstitution Symbol arity Gamma Delta)
    (a : MarkedTerm Symbol arity Delta sigma) :
    substituteTerm (renameTerm q (Renaming.weaken Gamma sigma)) (extendEnvironment s a)=substituteTerm q s := by
  have H := RenamingEquivarianceBindingProof.substitutionCovariance Symbol arity
    Gamma (sigma::Gamma) Delta Delta tau q (Renaming.weaken Gamma sigma) (fun v => v)
    s (extendEnvironment s a)
    (fun {_} v => (SourceMarkedBindingProof.markedRenamingIdentity.1 Symbol arity Delta _ (s v)).symm)
  exact H.trans (SourceMarkedBindingProof.markedRenamingIdentity.1 Symbol arity Delta tau _)

theorem consumedBinderEnvironment : ProtectedApplyTargets.ConsumedBinderEnvironment := by
  intro Symbol arity Gamma Delta pre s consumed sigma a
  funext tau v
  cases v with
  | here => rfl
  | there v =>
    exact dropClosing (liftFree pre s v) (closePrefix consumed) a

theorem emptyTuple : ProtectedApplyTargets.EmptyTuple := by
  intro Symbol arity Gamma Delta sigma q mask s
  cases q <;> rfl

theorem boundNameLift {Gamma Delta pre : List Ty} (s : MarkedSubstitution Symbol arity Gamma Delta)
    {tau : Ty} (v : Variable pre tau) : liftFree pre s (boundVariable Gamma v)=.var (boundVariable Delta v) := by
  induction v with
  | here => rfl
  | there v ih =>
    simp only [boundVariable,liftFree,liftSubstitution,ih,renameTerm,Renaming.weaken]
    rfl

theorem variableSplit (pre Gamma : List Ty) : ∀ {tau : Ty} (v : Variable (pre++Gamma) tau),
    (∃ w : Variable pre tau,v=boundVariable Gamma w) ∨
      (∃ w : Variable Gamma tau,v=freeRename pre Gamma w) := by
  induction pre with
  | nil => intro tau v; exact Or.inr ⟨v,rfl⟩
  | cons sigma pre ih =>
    intro tau v
    cases v with
    | here => exact Or.inl ⟨.here,rfl⟩
    | there v =>
      rcases ih v with ⟨w,rfl⟩ | ⟨w,rfl⟩
      · exact Or.inl ⟨.there w,rfl⟩
      · exact Or.inr ⟨w,rfl⟩

theorem closeOld {Gamma Delta pre : List Ty} (s : MarkedSubstitution Symbol arity Gamma Delta)
    (consumed : Arguments Symbol arity Delta pre) {tau : Ty} (v : Variable Gamma tau) :
    closeFree s consumed (freeRename pre Gamma v)=s v := by
  unfold closeFree
  rw [ProtectedPrefixProof.oldNameLift Symbol arity Gamma Delta pre s tau v]
  exact ProtectedPrefixProof.raisedSourceClosing Symbol arity Delta pre consumed tau (s v)

end LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedApplyBindingProof
