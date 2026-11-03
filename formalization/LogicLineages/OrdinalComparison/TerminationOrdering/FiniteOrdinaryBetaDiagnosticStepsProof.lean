module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FiniteOrdinaryBetaDiagnosticTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveComparisonProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FiniteOrdinaryBetaDiagnosticStepsProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication RecursiveComparison
open FiniteOrdinaryBetaDiagnostic

theorem ordinarySteps : FiniteOrdinaryBetaDiagnosticTargets.ActualFiniteOrdinarySteps := by
  have hz : Weak (Fin 4) arity above [] ⟨.ground,z⟩ ⟨.ground,z⟩ :=
    Weak.fun_ (arity := arity) (.ranked 0) (.ranked 0) .nil .nil [] rfl rfl (.refl _) .nil
  have hh : Weak (Fin 4) arity above [] ⟨.ground,h⟩ ⟨.ground,h⟩ :=
    Weak.fun_ (arity := arity) (.ranked 1) (.ranked 1) .nil .nil [] rfl rfl (.refl _) .nil
  have hk : Weak (Fin 4) arity above [] ⟨.ground,k⟩ ⟨.ground,k⟩ :=
    .fun_ (.ranked 2) (.ranked 2) (.cons h .nil) (.cons h .nil) [⟨.ground,h⟩]
      rfl rfl (.refl _) (.cons _ _ _ _ hh .nil)
  have hqk : Weak (Fin 4) arity above [] ⟨.ground,q⟩ ⟨.ground,k⟩ :=
    .select (.application .ground .ground) applicationBase [] .nil [] k k k rfl
      (by simp [applicationBase,argumentList]) rfl hk
  have hst : Weak (Fin 4) arity above [] ⟨.ground,s⟩ ⟨.ground,t⟩ :=
    .fun_ (.ranked 3) (.ranked 3) (.cons q (.cons z .nil)) (.cons k (.cons z .nil))
      [⟨.ground,k⟩,⟨.ground,z⟩] rfl rfl (.refl _) (.cons _ _ _ _ hqk (.cons _ _ _ _ hz .nil))
  have hpt : Weak (Fin 4) arity above [] ⟨.ground,p⟩ ⟨.ground,t⟩ :=
    .put (.application .ground .ground) applicationBase t
      (.select (.application .ground .ground) applicationBase [] .nil [.ground]
        (.lam (embed bodyOriginal)) s t rfl
        (by simp [applicationBase,argumentList]) rfl hst)
  let mk := MarkedTerm.marked (arity := arity) (.ranked 2) .ground (.cons h .nil) [] .nil
  have hmk : Weak (Fin 4) arity above [] ⟨.ground,mk⟩ ⟨.ground,h⟩ :=
    .select (.ranked 2) (.cons h .nil) [] .nil [] h h h rfl
      (by simp [argumentList]) rfl hh
  have hkh : Weak (Fin 4) arity above [] ⟨.ground,k⟩ ⟨.ground,h⟩ :=
    .put (.ranked 2) (.cons h .nil) h hmk
  have hstrict : Strict (Fin 4) arity above [] ⟨.ground,k⟩ ⟨.ground,h⟩ := .mark k mk h rfl hmk
  let mt := MarkedTerm.marked (arity := arity) (.ranked 3) .ground (.cons k (.cons z .nil)) [] .nil
  have hmth : Weak (Fin 4) arity above [] ⟨.ground,mt⟩ ⟨.ground,h⟩ :=
    .select (.ranked 3) (.cons k (.cons z .nil)) [] .nil [] k k h rfl
      (by simp [argumentList]) rfl hkh
  have hmul : StrictMultiset (Fin 4) arity above [] [⟨.ground,k⟩,⟨.ground,z⟩] [⟨.ground,h⟩,⟨.ground,h⟩] :=
    .replace _ _ [] [] _ _ (.refl _) (.refl _) (by intro he; cases he) .nil
      (.cons _ _ _ _ (List.mem_cons_self ..) hstrict
        (.cons _ _ _ _ (List.mem_cons_self ..) hstrict (.nil _)))
  have hmtu : Weak (Fin 4) arity above [] ⟨.ground,mt⟩ ⟨.ground,u⟩ :=
    .stat (.ranked 3) (.ranked 3) (.cons k (.cons z .nil)) [] .nil (.cons h (.cons h .nil))
      rfl hmul (by intro v hv; simp only [argumentList,List.mem_cons,List.not_mem_nil,or_false,or_self] at hv; subst v; exact hmth)
  exact ⟨hpt,.mark t mt u rfl hmtu⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.FiniteOrdinaryBetaDiagnosticStepsProof
