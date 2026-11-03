module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedRelatedSubstitutionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedRelatedSubstitutionSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding RecursiveComparison
open SourceExtendedSubstitution SourceExtendedRelatedSubstitution

theorem variableSubstitution {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty} {tau : Ty}
    (q : MarkedTerm Symbol arity Gamma tau) (rho : Renaming Gamma Delta) :
    substituteTerm q (fun v => .var (rho v))=renameTerm q rho := by
  have H := RenamingEquivarianceBindingProof.substitutionCovariance Symbol arity Gamma Gamma Gamma Delta tau q
    (fun v => v) rho (fun v => .var v) (fun v => .var (rho v)) (by intros; rfl)
  simpa only [SourceMarkedBindingProof.markedRenamingIdentity.1,SourceMarkedBindingProof.markedSubstitutionIdentity.1] using H

theorem renameWeak {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (above : Symbol → Symbol → Prop) (s t : Packed Symbol arity Gamma)
    (h : SourceExtendedComparison.Weak Symbol arity above Gamma s t) (rho : Renaming Gamma Delta) :
    SourceExtendedComparison.Weak Symbol arity above Delta ⟨s.1,renameTerm s.2 rho⟩ ⟨t.1,renameTerm t.2 rho⟩ := by
  have H := SourceExtendedSubstitutionProof.weakCovariance Symbol arity above Gamma Delta (fun v => .var (rho v)) s t h
  simpa only [substitutePacked,variableSubstitution] using H

theorem liftRelated {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (above : Symbol → Symbol → Prop) (theta eta : MarkedSubstitution Symbol arity Gamma Delta)
    (H : EnvironmentsRelated above theta eta) (sigma : Ty) :
    EnvironmentsRelated above (liftSubstitution (τ := sigma) theta) (liftSubstitution eta) := by
  intro tau v
  cases v with
  | here => exact .var .here
  | there v => exact renameWeak above _ _ (H _ v) (Renaming.weaken Delta sigma)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedRelatedSubstitutionSupportProof
