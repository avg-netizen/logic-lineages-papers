module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalAngleTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedApplyBindingProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalAngleSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open NumberedRewriteSyntax NumberedRewriteReduction NumberedRewriteApplication NumberedOriginalAngle

theorem transportRepresentation {Symbol : Type} {arity : Symbol → Nat} {n : Nat} {Gamma : List Ty}
    {sigma tau : Ty} (h : sigma=tau) (q : MarkedTerm Symbol arity Gamma sigma) (Q : AuxTerm Symbol arity Gamma sigma)
    (hq : Represents Symbol arity n Gamma sigma q Q) :
    Represents Symbol arity n Gamma tau (transportTerm h q) (transportAux h Q) := by
  cases h
  exact hq

theorem transportPaths {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop} {Gamma : List Ty}
    {sigma tau : Ty} (h : sigma=tau) {Q R : AuxTerm Symbol arity Gamma sigma}
    (hp : RawSteps Symbol arity above Gamma sigma Q R) :
    RawSteps Symbol arity above Gamma tau (transportAux h Q) (transportAux h R) := by
  cases h
  exact hp

theorem transportNumbered {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {sigma tau : Ty}
    (h : sigma=tau) (k : Nat) (f : Head Symbol) (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (types : List Ty) (extras : AuxArguments Symbol arity Gamma types) :
    transportAux h (.numbered k f sigma base types extras)=AuxTerm.numbered k f tau base types extras := by
  cases h
  rfl

theorem emptyOriginalWith {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty} {sigma tau : Ty}
    (q : MarkedTerm Symbol arity Gamma sigma) (env : MarkedSubstitution Symbol arity Gamma Delta) (h : sigma=tau) :
    applyOriginalWith q env .nil h=some (transportTerm h (substituteTerm q env)) := by
  cases q <;> rfl

theorem emptyAngle {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop) (n : Nat)
    {Gamma Delta : List Ty} {sigma tau : Ty} (q : MarkedTerm Symbol arity Gamma sigma)
    (env : MarkedSubstitution Symbol arity Gamma Delta) (suffix : sigma=tau) (r : MarkedTerm Symbol arity Delta tau)
    (h : applyOriginalWith q env .nil suffix=some r) (Q : AuxTerm Symbol arity Delta sigma)
    (values : AuxArguments Symbol arity Delta [])
    (hQ : Represents Symbol arity n Delta sigma (substituteTerm q env) Q) :
    ∃ R,RawSteps Symbol arity above Delta tau (NumberedRewriteReduction.applyArguments (transportAux suffix Q) values) R ∧
      Represents Symbol arity n Delta tau r R := by
  cases values
  have he : transportTerm suffix (substituteTerm q env)=r := Option.some.inj ((emptyOriginalWith q env suffix).symm.trans h)
  subst r
  exact ⟨transportAux suffix Q,.refl _,transportRepresentation suffix _ _ hQ⟩

theorem appendRepresentation {Symbol : Type} {arity : Symbol → Nat} {n : Nat} {Gamma xs ys : List Ty}
    (args : Arguments Symbol arity Gamma xs) (values : AuxArguments Symbol arity Gamma xs)
    (tail : Arguments Symbol arity Gamma ys) (tailValues : AuxArguments Symbol arity Gamma ys)
    (h : ArgumentsRepresent Symbol arity n Gamma xs args values)
    (ht : ArgumentsRepresent Symbol arity n Gamma ys tail tailValues) :
    ArgumentsRepresent Symbol arity n Gamma (xs++ys)
      (Source.SourceMarkedBinding.appendArguments args tail) (NumberedRewriteSyntax.appendArguments values tailValues) := by
  induction xs with
  | nil => cases h; exact ht
  | cons sigma xs ih => cases h with
    | cons q Q rest values hq hr => exact .cons _ _ _ _ hq (ih rest values hr)

theorem canonicalArgumentsRepresentation {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (n : Nat) (args : Arguments Symbol arity Gamma types) :
    ArgumentsRepresent Symbol arity n Gamma types args (canonicalArguments n args) := by
  induction types with
  | nil => cases args; exact .nil
  | cons sigma types ih => cases args with
    | cons q rest => exact .cons _ _ _ _ (NumberedRewriteSyntaxProof.canonicalNumbering Symbol arity n Gamma sigma q) (ih rest)

theorem consRepresentation {Symbol : Type} {arity : Symbol → Nat} {n : Nat} {Gamma types : List Ty} {sigma : Ty}
    (a : MarkedTerm Symbol arity Gamma sigma) (rest : Arguments Symbol arity Gamma types)
    (values : AuxArguments Symbol arity Gamma (sigma::types))
    (h : ArgumentsRepresent Symbol arity n Gamma (sigma::types) (.cons a rest) values) :
    ∃ A tail,values=AuxArguments.cons A tail ∧ Represents Symbol arity n Gamma sigma a A ∧
      ArgumentsRepresent Symbol arity n Gamma types rest tail := by
  cases h
  exact ⟨_,_,rfl,by assumption,by assumption⟩

theorem numberedRepresentation {Symbol : Type} {arity : Symbol → Nat} {n : Nat} {Gamma : List Ty} {sigma : Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity Gamma types) (Q : AuxTerm Symbol arity Gamma sigma)
    (h : Represents Symbol arity n Gamma sigma (.marked f sigma base types extras) Q) :
    ∃ k values extraValues,n≤k ∧ Q=AuxTerm.numbered k f sigma values types extraValues ∧
      ArgumentsRepresent Symbol arity n Gamma (headArguments arity f) base values ∧
      ArgumentsRepresent Symbol arity n Gamma types extras extraValues := by
  cases h
  exact ⟨_,_,_,by assumption,rfl,by assumption,by assumption⟩

theorem sourceBetaUnroll {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty} {sigma tau : Ty}
    (body : MarkedTerm Symbol arity (sigma::Gamma) tau) (env : MarkedSubstitution Symbol arity Gamma Delta)
    (a : MarkedTerm Symbol arity Delta sigma) :
    substituteTerm (substituteTerm body (Source.SourceMarkedBinding.liftSubstitution env))
      (extendEnvironment (fun v => .var v) a)=substituteTerm body (extendEnvironment env a) := by
  rw [ProtectedApplyBindingProof.substitutionComposition]
  apply congrArg (substituteTerm body)
  funext upsilon v
  cases v with
  | here => rfl
  | there v =>
    change substituteTerm (Source.SourceMarkedBinding.renameTerm (env v) (Renaming.weaken Delta sigma))
      (extendEnvironment (fun w => .var w) a)=env v
    rw [ProtectedApplyBindingProof.dropClosing]
    exact SourceMarkedBindingProof.markedSubstitutionIdentity.1 Symbol arity Delta upsilon (env v)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalAngleSupportProof
