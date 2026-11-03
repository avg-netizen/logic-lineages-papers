module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SuccessfulApplicationPostProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SuccessfulApplicationSourceProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison
open ProtectedApplyBindingProof SuccessfulApplicationPostProof

private theorem emptySource {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta Xi : List Ty} {tau : Ty}
    (q : MarkedTerm Symbol arity Gamma tau) (theta : MarkedSubstitution Symbol arity Gamma Delta)
    (env : MarkedSubstitution Symbol arity Delta Xi) (r : MarkedTerm Symbol arity Xi tau)
    (h : applyOriginalWith q (fun v => substituteTerm (theta v) env) .nil rfl=some r) :
    applyOriginalWith (substituteTerm q theta) env .nil rfl=some r := by
  rw [emptyWith] at h ⊢
  rw [substitutionComposition]
  exact h

theorem sourceSubstitution : SuccessfulApplicationSubstitutionTargets.SourceSubstitution := by
  intro Symbol arity Gamma Delta Xi sigma tau types q
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) generalizing Delta Xi tau types with
  | var v =>
    intro theta env args h r he
    cases args with
    | nil => cases h; exact emptySource (.var v) theta env r he
    | cons a rest => cases he
  | @lam Omega sigma upsilon body ih =>
    intro theta env args h r he
    cases args with
    | nil => cases h; exact emptySource (.lam body) theta env r he
    | cons a rest =>
      obtain ⟨hdom,hcod⟩ := Ty.arrow.inj h
      cases hdom
      cases hcod
      have henv : (fun {tau} (v : Variable (sigma::Omega) tau) =>
          substituteTerm (liftSubstitution theta v) (extendEnvironment env a))=
          (extendEnvironment (fun v => substituteTerm (theta v) env) a :
            MarkedSubstitution Symbol arity (sigma::Omega) Xi) := by
        funext tau v
        cases v with
        | here => rfl
        | there v => exact dropClosing (theta v) env a
      change applyOriginalWith (substituteTerm body (liftSubstitution theta))
        (extendEnvironment env a) rest rfl=some r
      apply ih _ _ _ _ (liftSubstitution theta) (extendEnvironment env a) rest rfl r
      rw [henv]
      exact he
  | ordinary hd base ih =>
    intro theta env args h r he
    cases args with
    | nil => cases h; exact emptySource (.ordinary hd base) theta env r he
    | cons a rest =>
      simpa only [substituteTerm,applyOriginalWith,argumentsComposition] using he
  | marked hd out base extraTypes extras ihb ihe =>
    intro theta env args h r he
    cases args with
    | nil => cases h; exact emptySource (.marked hd _ base extraTypes extras) theta env r he
    | cons a rest =>
      simpa only [substituteTerm,applyOriginalWith,argumentsComposition] using he
  | nil => trivial
  | cons q rest ihq ihr => trivial

end LogicLineages.OrdinalComparison.TerminationOrdering.SuccessfulApplicationSourceProof
