module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningInversionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningCompositionProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding RecursiveComparison SourceSharpening
open SourceSharpeningCompositionSupportProof
open SourceSharpeningInversionProof

theorem compositionMeaning {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (v : MarkedTerm Symbol arity Gamma tau) : CompositionMeaning v := by
  induction v using MarkedTerm.rec (motive_2 := fun _ _ args => ArgumentsMeaning args) with
  | var v =>
    intro q u hqu huv
    cases huv
    cases hqu
    exact .var v
  | lam body ih =>
    intro q u hqu huv
    obtain ⟨mid,heMid,hmid⟩ := lambdaInversion u (.lam body) huv _ _ body rfl
    obtain ⟨src,heSrc,hsrc⟩ := lambdaInversion q u hqu _ _ mid heMid
    have hq : q=MarkedTerm.lam src := by injection heSrc
    rw [hq]
    exact .lam src body (ih src mid hsrc hmid)
  | ordinary f base ih =>
    intro q u hqu huv
    obtain ⟨mid,heMid,hmid⟩ := ordinaryInversion u (.ordinary f base) huv f base rfl
    obtain ⟨src,heSrc,hsrc⟩ := ordinaryInversion q u hqu f mid heMid
    have hq : q=MarkedTerm.ordinary f src := by injection heSrc
    rw [hq]
    exact .ordinary f src base (ih.2 src mid hsrc hmid)
  | marked f tau base types extras ihb ihe =>
    intro q u hqu huv
    cases huv with
    | marked _ _ baseB _ typesB extrasB _ _ hBbase hBextras =>
      cases hqu with
      | marked _ _ baseQ _ typesQ extrasQ _ _ hQbase hQextras =>
        apply Sharp.marked f tau baseQ base typesQ extrasQ types extras
        · exact ihb.2 baseQ baseB hQbase hBbase
        · exact extrasCompose f baseQ baseB extrasQ extrasB extras
            (fun sigma => .marked f sigma baseQ baseB typesQ extrasQ typesB extrasB hQbase hQextras)
            hQextras hBextras ihe.1
  | nil =>
    constructor
    · intro p hp; cases hp
    · intro ss us hsu hut
      cases hut
      cases hsu
      exact .nil
  | cons q rest ihq ihr =>
    constructor
    · intro p hp
      rcases List.mem_cons.mp hp with he | hm
      · subst p; exact ihq
      · exact ihr.1 p hm
    · intro ss us hsu hut
      cases hut with
      | cons mid _ midRest _ hmid hmidRest =>
        cases hsu with
        | cons src _ srcRest _ hsrc hsrcRest =>
          exact .cons src q srcRest rest (ihq src mid hsrc hmid) (ihr.2 srcRest midRest hsrcRest hmidRest)

theorem transitivity : SourceSharpeningCompositionTargets.Transitivity := by
  intro Symbol arity Gamma tau q u v hqu huv
  exact compositionMeaning v q u hqu huv

private theorem listAppend {Symbol : Type} {arity : Symbol → Nat} {Gamma xs ys : List Ty}
    (a : Arguments Symbol arity Gamma xs) (b : Arguments Symbol arity Gamma ys) :
    argumentList (appendArguments a b)=argumentList a++argumentList b := by
  induction xs with
  | nil => cases a; rfl
  | cons tau xs ih =>
    cases a with
    | cons q rest => exact congrArg (List.cons ⟨tau,q⟩) (ih rest)

theorem additionalExtras : SourceSharpeningCompositionTargets.AdditionalExtras := by
  intro Symbol arity Gamma f tau base types moreTypes extras more
  apply Sharp.marked f tau base base (types++moreTypes) (appendArguments extras more) types extras
  · exact SourceSharpeningReflexivityProof.reflexiveArguments base
  · apply SourceSharpeningReflexivityProof.extrasFromArguments f base (appendArguments extras more) extras extras
      (SourceSharpeningReflexivityProof.reflexiveArguments extras)
    intro p hp
    rw [listAppend]
    exact List.mem_append_left _ hp

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningCompositionProof
