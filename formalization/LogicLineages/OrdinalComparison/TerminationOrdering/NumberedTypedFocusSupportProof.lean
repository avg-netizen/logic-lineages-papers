module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedFocusTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedFocusSupportProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedStepContexts NumberedTypedFocus

theorem argumentWithSound {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (visit : ∀ {tau},AuxTerm (Fin n) arity Gamma tau → Option (TermFocus n arity Gamma tau))
    (hv : ∀ tau (q : AuxTerm (Fin n) arity Gamma tau) result,visit q=some result → plug result.context result.value=q)
    {types : List Ty} (index : Nat) (args : AuxArguments (Fin n) arity Gamma types) :
    ∀ result,argumentFocusWith visit index args=some result → plugArguments result.context result.value=args := by
  induction index generalizing types with
  | zero =>
    cases args with
    | nil => intro result h; cases h
    | cons q rest =>
      intro result h
      simp only [argumentFocusWith,Option.map_eq_some_iff] at h
      obtain ⟨f,hf,rfl⟩ := h
      simp [plugArguments,hv _ q f hf]
  | succ index ih =>
    cases args with
    | nil => intro result h; cases h
    | cons q rest =>
      intro result h
      simp only [argumentFocusWith,Option.map_eq_some_iff] at h
      obtain ⟨f,hf,rfl⟩ := h
      simp [plugArguments,ih rest f hf]

theorem termFocusReconstruction : NumberedTypedFocusTargets.ActualTermFocusReconstruction := by
  intro n arity path
  induction path with
  | nil => intro Gamma tau q result h; simp only [focus,Option.some.injEq] at h; cases h; rfl
  | cons position path ih =>
    intro Gamma tau q result h
    cases position <;> cases q <;> try simp only [focus,Option.map_eq_some_iff] at h
    all_goals try contradiction
    case lam.lam body =>
      obtain ⟨f,hf,rfl⟩ := h
      simp [plug,ih _ _ body f hf]
    case appFunction.app arg fn =>
      obtain ⟨f,hf,rfl⟩ := h
      simp [plug,ih _ _ fn f hf]
    case ordinaryBase.ordinary index head base =>
      obtain ⟨f,hf,rfl⟩ := h
      have hi := argumentWithSound (fun q => focus path q) (fun tau q result he => ih _ tau q result he) index base f hf
      simp [plug,hi]
    case numberedBase.numbered index label head types base extras =>
      obtain ⟨f,hf,rfl⟩ := h
      have hi := argumentWithSound (fun q => focus path q) (fun tau q result he => ih _ tau q result he) index base f hf
      simp [plug,hi]
    case numberedExtras.numbered index label head types base extras =>
      obtain ⟨f,hf,rfl⟩ := h
      have hi := argumentWithSound (fun q => focus path q) (fun tau q result he => ih _ tau q result he) index extras f hf
      simp [plug,hi]

    all_goals
      unfold focus at h
      contradiction

theorem argumentFocusReconstruction : NumberedTypedFocusTargets.ActualArgumentFocusReconstruction := by
  intro n arity path index Gamma types args result h
  exact argumentWithSound (fun q => focus path q) (fun tau q result he => termFocusReconstruction n arity path Gamma tau q result he) index args result h

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedFocusSupportProof
