module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedSubstitutionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedSubstitutionSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison
open SourceExtendedSubstitution SuccessfulApplicationPostProof

theorem reflexiveTerm {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (above : Symbol → Symbol → Prop) (q : MarkedTerm Symbol arity Gamma tau) :
    SourceExtendedComparison.Weak Symbol arity above Gamma ⟨tau,q⟩ ⟨tau,q⟩ := by
  induction q using MarkedTerm.rec
    (motive_2 := fun Gamma types args => SourceExtendedComparison.WeakMatch Symbol arity above Gamma (argumentList args) (argumentList args))
  case var v => exact .var v
  case lam body ih => exact .abs body body ih
  case ordinary f base ih => exact .fun_ f f base base (argumentList base) rfl rfl (.refl _) ih
  case marked f tau base types extras ihb ihe => exact .in_ f f base base types extras types extras (argumentList base) rfl (.refl _) ihb ihe
  case nil => exact .nil
  case cons q rest ihq ihr => exact .cons _ _ _ _ ihq ihr

theorem argumentListSubstitution {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta types : List Ty}
    (args : Arguments Symbol arity Gamma types) (theta : MarkedSubstitution Symbol arity Gamma Delta) :
    argumentList (substituteArguments args theta)=(argumentList args).map (substitutePacked theta) := by
  induction types with
  | nil => cases args; rfl
  | cons tau types ih => cases args with
    | cons q rest => exact congrArg (List.cons (substitutePacked theta ⟨tau,q⟩)) (ih rest)

theorem selfSubstitution {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity Gamma types) (requested : List Ty)
    (theta : MarkedSubstitution Symbol arity Gamma Delta) :
    substituteArguments (selfArguments f base types extras requested) theta=
      selfArguments f (substituteArguments base theta) types (substituteArguments extras theta) requested := by
  induction requested with
  | nil => rfl
  | cons tau rest ih => exact congrArg (Arguments.cons (.marked f tau (substituteArguments base theta) types (substituteArguments extras theta))) ih

theorem openMarkedSubstitution {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (f : Head Symbol) (sigma tau : Ty) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity Gamma types)
    (theta : MarkedSubstitution Symbol arity Gamma Delta) :
    substituteTerm (openMarked f sigma tau base types extras) (liftSubstitution theta)=
      openMarked f sigma tau (substituteArguments base theta) types (substituteArguments extras theta) := by
  have hbase := RenamingEquivarianceBindingProof.argumentsCovariance base (Renaming.weaken Gamma sigma)
    (Renaming.weaken Delta sigma) theta (liftSubstitution theta) (by intros; rfl)
  have hextras := RenamingEquivarianceBindingProof.argumentsCovariance extras (Renaming.weaken Gamma sigma)
    (Renaming.weaken Delta sigma) theta (liftSubstitution theta) (by intros; rfl)
  simp only [openMarked,substituteTerm,substituteAppend,hbase,hextras,substituteArguments,liftSubstitution]

theorem prefixSubstitution {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta xs ys : List Ty}
    (pre : Arguments Symbol arity Gamma xs) (whole : Arguments Symbol arity Gamma ys)
    (h : SourceExtendedComparison.Prefix pre whole) (theta : MarkedSubstitution Symbol arity Gamma Delta) :
    SourceExtendedComparison.Prefix (substituteArguments pre theta) (substituteArguments whole theta) := by
  induction h with
  | nil whole => exact .nil _
  | cons q a b hp ih => exact .cons _ _ _ ih

theorem copiesSubstitution {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta xs ys : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (extras : Arguments Symbol arity Gamma xs) (copies : Arguments Symbol arity Gamma ys)
    (h : SourceExtendedComparison.PrefixCopies f base extras copies) (theta : MarkedSubstitution Symbol arity Gamma Delta) :
    SourceExtendedComparison.PrefixCopies f (substituteArguments base theta) (substituteArguments extras theta) (substituteArguments copies theta) := by
  induction h with
  | nil => exact .nil
  | cons tau preTypes restTypes pre rest hp hr ih => exact .cons _ _ _ _ _ (prefixSubstitution pre extras hp theta) ih

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedSubstitutionSupportProof
