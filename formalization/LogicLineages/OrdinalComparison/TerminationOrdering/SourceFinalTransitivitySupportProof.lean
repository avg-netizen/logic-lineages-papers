module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceFinalTransitivityTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceFinalTransitivitySupportProof
open Source Source.SourceMarkedSyntax RecursiveComparison SourceUnmarked SourceSharpeningInversionProof

def classAbove {Symbol : Type} (above : Symbol → Symbol → Prop) : HeadClass Symbol → HeadClass Symbol → Prop
  | .ranked f,.ranked g => above f g
  | .ranked _,.native | .ranked _,.application | .native,.application => True
  | _,_ => False

theorem headAboveClass {Symbol : Type} (above : Symbol → Symbol → Prop) (f g : Head Symbol) :
    headAbove above f g ↔ classAbove above (headClass f) (headClass g) := by
  cases f <;> cases g <;> rfl

theorem headAboveTransitive {Symbol : Type} (above : Symbol → Symbol → Prop) (H : Transitive above) :
    Transitive (headAbove above) := by
  intro f g h hfg hgh
  rw [headAboveClass] at hfg hgh ⊢
  generalize headClass f=cf at hfg ⊢
  generalize headClass g=cg at hfg hgh
  generalize headClass h=ch at hgh ⊢
  cases cf <;> cases cg <;> cases ch <;> simp only [classAbove] at * <;> try contradiction <;> try trivial
  exact H hfg hgh

theorem headAboveRightEquivalent {Symbol : Type} (above : Symbol → Symbol → Prop) (f g h : Head Symbol)
    (hfg : headAbove above f g) (hgh : headEquivalent g h) : headAbove above f h := by
  rw [headAboveClass] at hfg ⊢
  exact hgh ▸ hfg

theorem headAboveLeftEquivalent {Symbol : Type} (above : Symbol → Symbol → Prop) (f g h : Head Symbol)
    (hfg : headEquivalent f g) (hgh : headAbove above g h) : headAbove above f h := by
  rw [headAboveClass] at hgh ⊢
  exact hfg.symm ▸ hgh

theorem variableSource {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (s t : Packed Symbol arity Gamma)
    (h : SourceExtendedComparison.Weak Symbol arity above Gamma s t) :
    ∀ tau (v : Variable Gamma tau),s=⟨tau,.var v⟩ → t=⟨tau,.var v⟩ := by
  cases h <;> intro tau v he <;> try { have hn := congrArg rootShape he; cases hn }
  exact he

theorem unmarkedMarkabilityReflection {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (above : Symbol → Symbol → Prop) (q : MarkedTerm Symbol arity Gamma tau) :
    ∀ t : Packed Symbol arity Gamma,SourceExtendedComparison.Weak Symbol arity above Gamma ⟨tau,q⟩ t →
    Unmarked Symbol arity Gamma q → ∀ r : MarkedTerm Symbol arity Gamma t.1,strictMark t.2=some r →
      ∃ marked,strictMark q=some marked := by
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v =>
    intro t hw hq r hm
    have ht := variableSource above _ _ hw _ v rfl
    cases ht
    cases hm
  | @lam Gamma sigma tau body ih =>
    intro t hw hq r hm
    obtain ⟨target,ht,hbody⟩ := SourceExtendedMarkingSupportProof.lambdaSource above _ _ hw sigma tau body rfl
    cases ht
    have hUnmarked := SourceExtendedInversionProof.unmarkedLambda (.lam body) hq sigma tau body rfl
    cases hmt : strictMark target with
    | none => simp only [strictMark,hmt,Option.map_none] at hm; cases hm
    | some out =>
      obtain ⟨marked,hmark⟩ := ih ⟨tau,target⟩ hbody hUnmarked out hmt
      exact ⟨.lam marked,by simp only [strictMark,hmark,Option.map_some]⟩
  | ordinary f base ih => intro t hw hq r hm; exact ⟨.marked f _ base [] .nil,rfl⟩
  | marked f output base types extras ihb ihe =>
    intro t hw hq r hm
    exact (SourceExtendedInversionProof.notMarked f output base extras hq).elim
  | nil => trivial
  | cons q rest ihq ihr => trivial

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceFinalTransitivitySupportProof
