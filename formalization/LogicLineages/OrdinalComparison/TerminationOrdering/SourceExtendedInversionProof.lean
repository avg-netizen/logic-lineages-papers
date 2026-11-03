module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedRefinementProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedInversionProof
open Source Source.SourceMarkedSyntax RecursiveComparison SourceSharpening SourceUnmarked SourceExtendedElimination
open SourceSharpeningInversionProof

theorem unmarkedShape {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : MarkedTerm Symbol arity Gamma tau) (h : Unmarked Symbol arity Gamma q) : rootShape ⟨tau,q⟩≠3 := by
  cases h <;> simp [rootShape]

theorem notMarked {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (f : Head Symbol) (tau : Ty) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (extras : Arguments Symbol arity Gamma types) : ¬ Unmarked Symbol arity Gamma (.marked f tau base types extras) := by
  intro h
  exact unmarkedShape _ h rfl

theorem unmarkedLambda {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : MarkedTerm Symbol arity Gamma tau) (h : Unmarked Symbol arity Gamma q) :
    ∀ sigma upsilon (body : MarkedTerm Symbol arity (sigma::Gamma) upsilon),
    (⟨tau,q⟩ : Packed Symbol arity Gamma)=⟨.arrow sigma upsilon,.lam body⟩ →
      Unmarked Symbol arity (sigma::Gamma) body := by
  cases h with
  | var v => intro sigma upsilon body he; have hh := congrArg rootShape he; simp [rootShape] at hh
  | lam actual hbody =>
    intro sigma upsilon body he
    obtain ⟨hdom,hcod⟩ := Ty.arrow.inj (congrArg Sigma.fst he)
    cases hdom
    cases hcod
    have ht : MarkedTerm.lam actual=MarkedTerm.lam body := by injection he
    have hb : actual=body := by injection ht
    exact hb ▸ hbody
  | ordinary f base hbase => intro sigma upsilon body he; have hh := congrArg rootShape he; simp [rootShape] at hh

theorem unmarkedOrdinary {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : MarkedTerm Symbol arity Gamma tau) (h : Unmarked Symbol arity Gamma q) :
    ∀ (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f)),
    (⟨tau,q⟩ : Packed Symbol arity Gamma)=⟨headResult f,.ordinary f base⟩ → ArgumentsUnmarked Symbol arity Gamma base := by
  cases h with
  | var v => intro f base he; have hh := congrArg rootShape he; simp [rootShape] at hh
  | lam body hbody => intro f base he; have hh := congrArg rootShape he; simp [rootShape] at hh
  | ordinary g actual hactual =>
    intro f base he
    have hf : g=f := Option.some.inj (congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) he)
    cases hf
    have ht : MarkedTerm.ordinary g actual=MarkedTerm.ordinary g base := by injection he
    have hb : actual=base := by injection ht
    exact hb ▸ hactual

theorem markedSource {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q u : MarkedTerm Symbol arity Gamma tau) (h : Sharp Symbol arity Gamma q u) :
    ∀ (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
      (types : List Ty) (extras : Arguments Symbol arity Gamma types),
    (⟨tau,u⟩ : Packed Symbol arity Gamma)=⟨tau,.marked f tau base types extras⟩ →
    ∃ (baseQ : Arguments Symbol arity Gamma (headArguments arity f)) (typesQ : List Ty)
      (extrasQ : Arguments Symbol arity Gamma typesQ),
    (⟨tau,q⟩ : Packed Symbol arity Gamma)=⟨tau,.marked f tau baseQ typesQ extrasQ⟩ ∧
      ArgumentsSharp Symbol arity Gamma baseQ base ∧ ExtrasSharp Symbol arity Gamma f baseQ typesQ extrasQ extras := by
  cases h with
  | var v => intro f base types extras he; have hh := congrArg rootShape he; simp [rootShape] at hh
  | lam s t hs => intro f base types extras he; have hh := congrArg rootShape he; simp [rootShape] at hh
  | ordinary g ss ts hs => intro f base types extras he; have hh := congrArg rootShape he; simp [rootShape] at hh
  | marked g tau baseQ baseT typesQ extrasQ typesT extrasT hb he =>
    intro f base types extras hp
    have hf : g=f := Option.some.inj (congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) hp)
    cases hf
    have ht : MarkedTerm.marked g tau baseT typesT extrasT=MarkedTerm.marked g tau base types extras := by injection hp
    cases ht
    exact ⟨baseQ,typesQ,extrasQ,rfl,hb,he⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedInversionProof
