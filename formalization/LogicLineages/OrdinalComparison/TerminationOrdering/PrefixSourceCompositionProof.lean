module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PrefixSourceCompositionSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PrefixSourceCompositionProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison SourceSharpening
open PrefixSourceComposition PrefixSourceCompositionSupportProof SourceSharpeningInversionProof

theorem guardedSourceComposition : PrefixSourceCompositionTargets.ActualGuardedSourceComposition := by
  intro Symbol arity Gamma Delta Xi f base extraTypes extras sigma tau types q
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) generalizing Delta tau types with
  | var v =>
    intro theta env args H hc suffix r hr
    cases args with
    | nil => cases suffix; exact .inl (emptyComposition (.var v) theta env r hr)
    | cons a rest =>
      cases hi : theta v with
      | var w => simp only [substituteTerm,hi,applyOriginalWith] at hr; cases hr
      | lam body =>
        have hs := imageShape f base extras (substituteTerm (theta v) env) (H _ v)
        simp only [hi,substituteTerm,rootShape] at hs
        rcases hs with hs | hs <;> cases hs
      | ordinary g bs =>
        have hs := imageShape f base extras (substituteTerm (theta v) env) (H _ v)
        simp only [hi,substituteTerm,rootShape] at hs
        rcases hs with hs | hs <;> cases hs
      | marked g output bs ets es =>
        have hnorm : applyOriginalWith (substituteTerm (theta v) env) (fun v => .var v) (.cons a rest) suffix=some r := by
          simpa only [substituteTerm,hi,applyOriginalWith,SourceMarkedBindingProof.markedSubstitutionIdentity.2] using hr
        rcases H _ v with ⟨w,hw⟩ | ⟨preTypes,pre,hp,he⟩
        · have hs := congrArg (fun q => rootShape (⟨_,q⟩ : Packed Symbol arity Xi)) hw
          simp only [hi,substituteTerm,rootShape] at hs
          cases hs
        · rw [he] at hnorm
          exact .inr (prefixApplication f base extras pre hp (.cons a rest) hc _ tau suffix r hnorm)
  | @lam Omega sigma upsilon body ih =>
    intro theta env args H hc suffix r hr
    cases args with
    | nil => cases suffix; exact .inl (emptyComposition (.lam body) theta env r hr)
    | cons a rest =>
      obtain ⟨hdom,hcod⟩ := Ty.arrow.inj suffix
      cases hdom
      cases hcod
      cases hc with
      | cons argType preTypes restTypes pre rest hp hrest =>
        have hext : (fun {tau} (v : Variable (sigma::Omega) tau) =>
            substituteTerm (liftSubstitution theta v) (extendEnvironment env (.marked f sigma base preTypes pre)))=
            (extendEnvironment (fun v => substituteTerm (theta v) env) (.marked f sigma base preTypes pre) :
              MarkedSubstitution Symbol arity (sigma::Omega) Xi) := by
          funext tau v
          cases v with
          | here => rfl
          | there v => exact ProtectedApplyBindingProof.dropClosing (theta v) env (.marked f sigma base preTypes pre)
        have Hext : ∀ upsilon (v : Variable (sigma::Omega) upsilon),
            PrefixImage f base extras (substituteTerm (liftSubstitution theta v) (extendEnvironment env (.marked f sigma base preTypes pre))) := by
          intro upsilon v
          have hv := congrArg (fun environment : MarkedSubstitution Symbol arity (sigma::Omega) Xi => environment v) hext
          rw [hv]
          cases v with
          | here => exact .inr ⟨preTypes,pre,hp,rfl⟩
          | there v => exact H _ v
        have hres := ih _ _ _ (liftSubstitution theta) (extendEnvironment env (.marked f sigma base preTypes pre)) rest Hext hrest rfl r hr
        rcases hres with hout | hsharp
        · apply Or.inl
          change applyOriginalWith body (extendEnvironment (fun v => substituteTerm (theta v) env) (.marked f sigma base preTypes pre)) rest rfl=some r
          rw [←hext]
          exact hout
        · exact .inr hsharp
  | ordinary g bs ih =>
    intro theta env args H hc suffix r hr
    cases args with
    | nil => cases suffix; exact .inl (emptyComposition (.ordinary g bs) theta env r hr)
    | cons a rest => exact .inl (by simpa only [substituteTerm,applyOriginalWith,ProtectedApplyBindingProof.argumentsComposition] using hr)
  | marked g output bs ets es ihb ihe =>
    intro theta env args H hc suffix r hr
    cases args with
    | nil => cases suffix; exact .inl (emptyComposition (.marked g _ bs ets es) theta env r hr)
    | cons a rest => exact .inl (by simpa only [substituteTerm,applyOriginalWith,ProtectedApplyBindingProof.argumentsComposition] using hr)
  | nil => trivial
  | cons q rest ihq ihr => trivial

end LogicLineages.OrdinalComparison.TerminationOrdering.PrefixSourceCompositionProof
