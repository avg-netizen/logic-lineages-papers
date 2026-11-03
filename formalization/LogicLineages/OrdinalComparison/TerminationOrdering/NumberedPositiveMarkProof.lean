module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPositiveMarkTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPositiveMarkProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction

theorem lowerArguments {Symbol : Type} {arity : Symbol → Nat} {n m : Nat} {Gamma types : List Ty}
    (hmn : m≤n) (args : Arguments Symbol arity Gamma types) (values : AuxArguments Symbol arity Gamma types)
    (h : ArgumentsRepresent Symbol arity n Gamma types args values) : ArgumentsRepresent Symbol arity m Gamma types args values := by
  induction types with
  | nil => cases h; exact .nil
  | cons sigma types ih => cases h with
    | cons q Q rest values hq hr =>
      exact .cons _ _ _ _ (NumberedRewriteSyntaxProof.budgetLowering Symbol arity n m hmn Gamma sigma q Q hq)
        (ih rest values hr)

def sourceShape {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} :
    RecursiveComparison.Packed Symbol arity Gamma → Nat
  | ⟨_,.var _⟩ => 0
  | ⟨_,.lam _⟩ => 1
  | ⟨_,.ordinary _ _⟩ => 2
  | ⟨_,.marked _ _ _ _ _⟩ => 3

theorem lambdaRepresentation {Symbol : Type} {arity : Symbol → Nat} {n : Nat} {Gamma : List Ty} {tau : Ty}
    (q : MarkedTerm Symbol arity Gamma tau) (Q : AuxTerm Symbol arity Gamma tau)
    (h : Represents Symbol arity n Gamma tau q Q) :
    ∀ sigma upsilon (body : MarkedTerm Symbol arity (sigma::Gamma) upsilon),
    (⟨tau,q⟩ : RecursiveComparison.Packed Symbol arity Gamma)=⟨.arrow sigma upsilon,.lam body⟩ →
    ∃ B : AuxTerm Symbol arity (sigma::Gamma) upsilon,
      (⟨tau,Q⟩ : NumberedRewriteReduction.Packed Symbol arity Gamma)=⟨.arrow sigma upsilon,.lam B⟩ ∧
      Represents Symbol arity n (sigma::Gamma) upsilon body B := by
  cases h
  case lam source target hb =>
    intro sigma upsilon body he
    obtain ⟨hdom,hcod⟩ := Ty.arrow.inj (congrArg Sigma.fst he)
    cases hdom
    cases hcod
    have hs : MarkedTerm.lam source=MarkedTerm.lam body := by injection he
    have hbody : source=body := by injection hs
    subst source
    exact ⟨target,rfl,hb⟩
  all_goals
    intro sigma upsilon body he
    have hn := congrArg sourceShape he
    cases hn

theorem ordinaryRepresentation {Symbol : Type} {arity : Symbol → Nat} {n : Nat} {Gamma : List Ty} {tau : Ty}
    (q : MarkedTerm Symbol arity Gamma tau) (Q : AuxTerm Symbol arity Gamma tau)
    (h : Represents Symbol arity n Gamma tau q Q) :
    ∀ (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f)),
    (⟨tau,q⟩ : RecursiveComparison.Packed Symbol arity Gamma)=⟨headResult f,.ordinary f base⟩ →
    ∃ values : AuxArguments Symbol arity Gamma (headArguments arity f),
      (⟨tau,Q⟩ : NumberedRewriteReduction.Packed Symbol arity Gamma)=⟨headResult f,.ordinary f values⟩ ∧
      ArgumentsRepresent Symbol arity n Gamma (headArguments arity f) base values := by
  cases h
  case ordinary g source values hb =>
    intro f base he
    have hg : g=f := Option.some.inj (congrArg (fun p : RecursiveComparison.Packed Symbol arity Gamma => spineHead p.2) he)
    cases hg
    have hs : MarkedTerm.ordinary g source=MarkedTerm.ordinary g base := by injection he
    have hbase : source=base := by injection hs
    subst source
    exact ⟨values,rfl,hb⟩
  all_goals
    intro f base he
    have hn := congrArg sourceShape he
    cases hn

theorem rawPositiveMark : NumberedPositiveMarkTargets.ActualRawPositiveMark := by
  intro Symbol arity above n Gamma tau q
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v => intro r hm Q hQ; cases hm
  | @lam Gamma sigma tau body ih =>
    intro r hm Q hQ
    cases hbody : RecursiveComparison.strictMark body with
    | none => simp only [RecursiveComparison.strictMark,hbody,Option.map_none] at hm; cases hm
    | some marked =>
      simp only [RecursiveComparison.strictMark,hbody,Option.map_some] at hm
      have he : MarkedTerm.lam marked=r := Option.some.inj hm
      subst r
      obtain ⟨B,hQpacked,hB⟩ := lambdaRepresentation (.lam body) Q hQ sigma tau body rfl
      have hQeq : Q=AuxTerm.lam B := by injection hQpacked
      subst Q
      obtain ⟨R,hstep,hR⟩ := ih marked hbody B hB
      exact ⟨.lam R,.lam B R hstep,.lam marked R hR⟩
  | ordinary f base ih =>
    intro r hm Q hQ
    have he : MarkedTerm.marked f (headResult f) base [] .nil=r := Option.some.inj hm
    subst r
    obtain ⟨values,hQpacked,hvalues⟩ := ordinaryRepresentation (.ordinary f base) Q hQ f base rfl
    have hQeq : Q=AuxTerm.ordinary f values := by injection hQpacked
    subst Q
    exact ⟨.numbered n f (headResult f) values [] .nil,.put n f values,
      .numbered f (headResult f) base values [] .nil .nil n (Nat.le_refl _)
        (lowerArguments (Nat.le_succ n) base values hvalues) .nil⟩
  | marked f output base types extras ihb ihe => intro r hm Q hQ; cases hm
  | nil => trivial
  | cons q rest ihq ihr => trivial

theorem ordinaryPositiveMark : NumberedPositiveMarkTargets.ActualOrdinaryPositiveMark := by
  intro Symbol arity above n Gamma tau q r hm
  exact rawPositiveMark Symbol arity above n Gamma tau (embed q) r hm (translateOriginal q)
    (NumberedRewriteSyntaxProof.ordinaryTranslation Symbol arity (n+1) Gamma tau q)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPositiveMarkProof
