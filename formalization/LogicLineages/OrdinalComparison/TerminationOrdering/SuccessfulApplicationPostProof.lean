module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SuccessfulApplicationSubstitutionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SuccessfulApplicationPostProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison
open ProtectedApplyBindingProof

theorem emptyWith {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty} {tau : Ty}
    (q : MarkedTerm Symbol arity Gamma tau) (env : MarkedSubstitution Symbol arity Gamma Delta) :
    applyOriginalWith q env .nil rfl=some (substituteTerm q env) := by cases q <;> rfl

theorem substituteAppend {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta xs ys : List Ty}
    (a : Arguments Symbol arity Gamma xs) (b : Arguments Symbol arity Gamma ys)
    (theta : MarkedSubstitution Symbol arity Gamma Delta) :
    substituteArguments (appendArguments a b) theta=
      appendArguments (substituteArguments a theta) (substituteArguments b theta) := by
  induction xs with
  | nil => cases a; rfl
  | cons tau xs ih =>
    cases a with
    | cons q rest => exact congrArg (Arguments.cons (substituteTerm q theta)) (ih rest)

private theorem emptyPost {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta Xi : List Ty} {tau : Ty}
    (q : MarkedTerm Symbol arity Gamma tau) (env : MarkedSubstitution Symbol arity Gamma Delta)
    (post : MarkedSubstitution Symbol arity Delta Xi) (r : MarkedTerm Symbol arity Delta tau)
    (h : applyOriginalWith q env .nil rfl=some r) :
    applyOriginalWith q (fun v => substituteTerm (env v) post) .nil rfl=some (substituteTerm r post) := by
  have hr : substituteTerm q env=r := Option.some.inj ((emptyWith q env).symm.trans h)
  rw [emptyWith,← hr,substitutionComposition]

theorem postSubstitution : SuccessfulApplicationSubstitutionTargets.PostSubstitution := by
  intro Symbol arity Gamma Delta Xi sigma tau types q
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) generalizing Delta Xi tau types with
  | var v =>
    intro env args h r post he
    cases args with
    | nil => cases h; exact emptyPost (.var v) env post r he
    | cons a rest => cases he
  | @lam Omega sigma upsilon body ih =>
    intro env args h r post he
    cases args with
    | nil => cases h; exact emptyPost (.lam body) env post r he
    | cons a rest =>
      obtain ⟨hdom,hcod⟩ := Ty.arrow.inj h
      cases hdom
      cases hcod
      have henv : (fun {tau} (v : Variable (sigma::Omega) tau) =>
          substituteTerm (extendEnvironment env a v) post)=
          (extendEnvironment (fun v => substituteTerm (env v) post) (substituteTerm a post) :
            MarkedSubstitution Symbol arity (sigma::Omega) Xi) := by
        funext tau v
        cases v <;> rfl
      change applyOriginalWith body
        (extendEnvironment (fun v => substituteTerm (env v) post) (substituteTerm a post))
        (substituteArguments rest post) rfl=some (substituteTerm r post)
      rw [← henv]
      exact ih _ _ _ _ (extendEnvironment env a) rest rfl r post he
  | ordinary hd base ih =>
    intro env args h r post he
    cases args with
    | nil => cases h; exact emptyPost (.ordinary hd base) env post r he
    | cons a rest =>
      have hr : .marked hd tau (substituteArguments base env) _ (.cons a rest)=r := Option.some.inj he
      subst r
      simp only [applyOriginalWith,substituteTerm,substituteArguments,argumentsComposition]
  | marked hd out base extraTypes extras ihb ihe =>
    intro env args h r post he
    cases args with
    | nil => cases h; exact emptyPost (.marked hd _ base extraTypes extras) env post r he
    | cons a rest =>
      have hr : .marked hd tau (substituteArguments base env) _
          (appendArguments (substituteArguments extras env) (.cons a rest))=r := Option.some.inj he
      subst r
      simp only [applyOriginalWith,substituteTerm,substituteArguments,argumentsComposition,substituteAppend]
  | nil => trivial
  | cons q rest ihq ihr => trivial

theorem strictMarkSubstitution : SuccessfulApplicationSubstitutionTargets.StrictMarkSubstitution := by
  intro Symbol arity Gamma Delta tau q
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) generalizing Delta with
  | var v => intro r theta h; cases h
  | lam body ih =>
    intro r theta h
    cases hm : strictMark body with
    | none => simp only [strictMark,hm,Option.map_none] at h; cases h
    | some result =>
      simp only [strictMark,hm,Option.map_some] at h
      have hr : MarkedTerm.lam result=r := Option.some.inj h
      subst r
      simp only [substituteTerm,strictMark,ih _ result (liftSubstitution theta) hm,Option.map_some]
  | ordinary hd base ih =>
    intro r theta h
    have hr : .marked hd (headResult hd) base [] .nil=r := Option.some.inj h
    subst r
    rfl
  | marked hd out base extraTypes extras ihb ihe => intro r theta h; cases h
  | nil => trivial
  | cons q rest ihq ihr => trivial

end LogicLineages.OrdinalComparison.TerminationOrdering.SuccessfulApplicationPostProof
