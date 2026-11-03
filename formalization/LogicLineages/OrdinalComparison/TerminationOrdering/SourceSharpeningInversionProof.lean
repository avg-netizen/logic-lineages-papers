module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningCompositionSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningInversionProof
open Source Source.SourceMarkedSyntax RecursiveComparison SourceSharpening

def rootShape {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} : Packed Symbol arity Gamma → Nat
  | ⟨_,.var _⟩ => 0
  | ⟨_,.lam _⟩ => 1
  | ⟨_,.ordinary _ _⟩ => 2
  | ⟨_,.marked _ _ _ _ _⟩ => 3

/-- Keep the actual result type abstract during elimination; only afterwards
use the literal packed lambda equation. This avoids invalid inversion through
an unsolved equation involving the function headResult. -/
theorem lambdaInversion {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q u : MarkedTerm Symbol arity Gamma tau) (h : Sharp Symbol arity Gamma q u) :
    ∀ sigma upsilon (body : MarkedTerm Symbol arity (sigma::Gamma) upsilon),
    (⟨tau,u⟩ : Packed Symbol arity Gamma)=⟨.arrow sigma upsilon,.lam body⟩ →
    ∃ src : MarkedTerm Symbol arity (sigma::Gamma) upsilon,
      (⟨tau,q⟩ : Packed Symbol arity Gamma)=⟨.arrow sigma upsilon,.lam src⟩ ∧
      Sharp Symbol arity (sigma::Gamma) src body := by
  cases h with
  | var v =>
    intro sigma upsilon body he
    have hh := congrArg rootShape he
    simp [rootShape] at hh
  | lam src target hbody =>
    intro sigma upsilon body he
    obtain ⟨hdom,hcod⟩ := Ty.arrow.inj (congrArg Sigma.fst he)
    cases hdom
    cases hcod
    have ht : MarkedTerm.lam target=MarkedTerm.lam body := by injection he
    have hb : target=body := by injection ht
    subst body
    exact ⟨src,rfl,hbody⟩
  | ordinary f ss ts hb =>
    intro sigma upsilon body he
    have hh := congrArg rootShape he
    simp [rootShape] at hh
  | marked f tau ss ts typesS extrasS typesT extrasT hb he =>
    intro sigma upsilon body heq
    have hh := congrArg rootShape heq
    simp [rootShape] at hh

theorem ordinaryInversion {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q u : MarkedTerm Symbol arity Gamma tau) (h : Sharp Symbol arity Gamma q u) :
    ∀ (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f)),
    (⟨tau,u⟩ : Packed Symbol arity Gamma)=⟨headResult f,.ordinary f base⟩ →
    ∃ src : Arguments Symbol arity Gamma (headArguments arity f),
      (⟨tau,q⟩ : Packed Symbol arity Gamma)=⟨headResult f,.ordinary f src⟩ ∧
      ArgumentsSharp Symbol arity Gamma src base := by
  cases h with
  | var v =>
    intro f base he
    have hh := congrArg rootShape he
    simp [rootShape] at hh
  | lam s t hs =>
    intro f base he
    have hh := congrArg rootShape he
    simp [rootShape] at hh
  | ordinary g ss ts hb =>
    intro f base he
    have hf : g=f := by
      have hh := congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) he
      exact Option.some.inj hh
    cases hf
    have ht : MarkedTerm.ordinary g ts=MarkedTerm.ordinary g base := by injection he
    have hb' : ts=base := by injection ht
    subst base
    exact ⟨ss,rfl,hb⟩
  | marked g tau ss ts typesS extrasS typesT extrasT hb he =>
    intro f base heq
    have hh := congrArg rootShape heq
    simp [rootShape] at hh

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningInversionProof
