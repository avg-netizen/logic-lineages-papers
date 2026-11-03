module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinarySubstitutionStabilityTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinarySubstitutionStabilitySupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison
open OrdinarySubstitutionStability SuccessfulApplicationPostProof

theorem successfulOriginalApply : OrdinarySubstitutionStabilityTargets.SuccessfulOriginalApply := by
  intro Symbol arity Gamma Delta sigma tau types q args h r theta he
  have hp := SuccessfulApplicationPostProof.postSubstitution Symbol arity Gamma Gamma Delta
    sigma tau types q (fun v => .var v) args h r theta he
  have hi : (fun {tau} (v : Variable Gamma tau) => substituteTerm (theta v) (fun v => .var v))=(@theta) := by
    funext tau v
    exact SourceMarkedBindingProof.markedSubstitutionIdentity.1 Symbol arity Delta tau (theta v)
  apply SuccessfulApplicationSourceProof.sourceSubstitution Symbol arity Gamma Delta Delta sigma tau types
    q theta (fun v => .var v) (substituteArguments args theta) h (substituteTerm r theta)
  rw [hi]
  exact hp

theorem argumentListSubstitution {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta types : List Ty}
    (args : Arguments Symbol arity Gamma types) (theta : Substitution Symbol arity Gamma Delta) :
    argumentList (substituteArguments args (markedMap theta))=(argumentList args).map (substitutePacked theta) := by
  induction types with
  | nil => cases args; rfl
  | cons tau types ih =>
    cases args with
    | cons q rest => exact congrArg (List.cons (substitutePacked theta ⟨tau,q⟩)) (ih rest)

theorem selfSubstitution {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity Gamma types) (requested : List Ty)
    (theta : Substitution Symbol arity Gamma Delta) :
    substituteArguments (selfArguments f base types extras requested) (markedMap theta)=
      selfArguments f (substituteArguments base (markedMap theta)) types
        (substituteArguments extras (markedMap theta)) requested := by
  induction requested with
  | nil => rfl
  | cons tau rest ih => exact congrArg (Arguments.cons
      (.marked f tau (substituteArguments base (markedMap theta)) types
        (substituteArguments extras (markedMap theta)))) ih

theorem liftMap {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (theta : Substitution Symbol arity Gamma Delta) (sigma : Ty) :
    (@markedMap Symbol arity (sigma::Gamma) (sigma::Delta)
      (@Substitution.lift Symbol arity Gamma Delta sigma theta))=
      @liftSubstitution Symbol arity Gamma Delta sigma (markedMap theta) := by
  funext tau v
  cases v with
  | here => rfl
  | there v =>
    exact SourceMarkedBindingProof.embeddingRenaming Symbol arity Delta (sigma::Delta)
      tau (theta v) (Renaming.weaken Delta sigma)

theorem openMarkedSubstitution {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (f : Head Symbol) (sigma tau : Ty) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity Gamma types)
    (theta : Substitution Symbol arity Gamma Delta) :
    substituteTerm (openMarked f sigma tau base types extras) (markedMap (Substitution.lift theta))=
      openMarked f sigma tau (substituteArguments base (markedMap theta)) types
        (substituteArguments extras (markedMap theta)) := by
  rw [liftMap theta sigma]
  have hbase := RenamingEquivarianceBindingProof.argumentsCovariance base (Renaming.weaken Gamma sigma)
    (Renaming.weaken Delta sigma) (markedMap theta) (liftSubstitution (markedMap theta)) (by intros; rfl)
  have hextras := RenamingEquivarianceBindingProof.argumentsCovariance extras (Renaming.weaken Gamma sigma)
    (Renaming.weaken Delta sigma) (markedMap theta) (liftSubstitution (markedMap theta)) (by intros; rfl)
  simp only [openMarked,substituteTerm,substituteAppend,hbase,hextras,substituteArguments,liftSubstitution]

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinarySubstitutionStabilitySupportProof
