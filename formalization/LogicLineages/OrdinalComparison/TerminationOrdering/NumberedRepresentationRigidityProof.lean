module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRepresentationRigidityTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRepresentationRigidityProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction

theorem unmarkedLambda {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : MarkedTerm Symbol arity Gamma tau) (h : SourceUnmarked.Unmarked Symbol arity Gamma q) :
    ∀ sigma upsilon (body : MarkedTerm Symbol arity (sigma::Gamma) upsilon),
    (⟨tau,q⟩ : RecursiveComparison.Packed Symbol arity Gamma)=⟨.arrow sigma upsilon,.lam body⟩ →
      SourceUnmarked.Unmarked Symbol arity (sigma::Gamma) body := by
  cases h
  case lam source hb =>
    intro sigma upsilon body he
    obtain ⟨hdom,hcod⟩ := Ty.arrow.inj (congrArg Sigma.fst he)
    cases hdom
    cases hcod
    have hs : MarkedTerm.lam source=MarkedTerm.lam body := by injection he
    have hbody : source=body := by injection hs
    subst source
    exact hb
  all_goals
    intro sigma upsilon body he
    have hn := congrArg NumberedPositiveMarkProof.sourceShape he
    cases hn

theorem unmarkedOrdinary {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : MarkedTerm Symbol arity Gamma tau) (h : SourceUnmarked.Unmarked Symbol arity Gamma q) :
    ∀ (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f)),
    (⟨tau,q⟩ : RecursiveComparison.Packed Symbol arity Gamma)=⟨headResult f,.ordinary f base⟩ →
      SourceUnmarked.ArgumentsUnmarked Symbol arity Gamma base := by
  cases h
  case ordinary g source hb =>
    intro f base he
    have hg : g=f := Option.some.inj (congrArg (fun p : RecursiveComparison.Packed Symbol arity Gamma => spineHead p.2) he)
    cases hg
    have hs : MarkedTerm.ordinary g source=MarkedTerm.ordinary g base := by injection he
    have hbase : source=base := by injection hs
    subst source
    exact hb
  all_goals
    intro f base he
    have hn := congrArg NumberedPositiveMarkProof.sourceShape he
    cases hn

theorem unmarkedShape {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : MarkedTerm Symbol arity Gamma tau) (h : SourceUnmarked.Unmarked Symbol arity Gamma q) :
    NumberedPositiveMarkProof.sourceShape ⟨tau,q⟩ ≠ 3 := by
  cases h <;> simp only [NumberedPositiveMarkProof.sourceShape] <;> omega

theorem unmarkedRepresentation : NumberedRepresentationRigidityTargets.ActualUnmarkedRepresentation := by
  intro Symbol arity n Gamma tau q Q hu h
  refine Represents.rec
    (motive_1 := fun Gamma tau q Q _ => SourceUnmarked.Unmarked Symbol arity Gamma q → Q=canonical 0 q)
    (motive_2 := fun Gamma types args values _ =>
      SourceUnmarked.ArgumentsUnmarked Symbol arity Gamma args → values=canonicalArguments 0 args)
    ?_ ?_ ?_ ?_ ?_ ?_ h hu
  · intro Gamma sigma v _; rfl
  · intro Gamma sigma tau q Q _ ih hu
    exact congrArg AuxTerm.lam (ih (unmarkedLambda (.lam q) hu sigma tau q rfl))
  · intro Gamma f base values _ ih hu
    exact congrArg (AuxTerm.ordinary f) (ih (unmarkedOrdinary (.ordinary f base) hu f base rfl))
  · intro Gamma f output base values types extras extraValues k hk hb he ihb ihe hu
    exact False.elim (unmarkedShape (.marked f output base types extras) hu rfl)
  · intro Gamma _; rfl
  · intro Gamma sigma types q Q rest values hq hr ihq ihr hu
    cases hu with
    | cons _ _ hqu hru => exact congrArg₂ AuxArguments.cons (ihq hqu) (ihr hru)

theorem unmarkedArguments : NumberedRepresentationRigidityTargets.ActualUnmarkedArguments := by
  intro Symbol arity n Gamma types args values hu h
  induction types with
  | nil => cases h; rfl
  | cons sigma types ih =>
    cases h with
    | cons q Q rest values hq hr =>
      cases hu with
      | cons _ _ hqu hru =>
        exact congrArg₂ AuxArguments.cons
          (unmarkedRepresentation Symbol arity n Gamma sigma q Q hqu hq) (ih rest values hru hr)

theorem finiteMarkWitness : NumberedRepresentationRigidityTargets.ActualFiniteMark := by
  intro Symbol arity n Gamma tau q
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
      obtain ⟨B,hQpacked,hB⟩ := NumberedPositiveMarkProof.lambdaRepresentation (.lam body) Q hQ sigma tau body rfl
      have hQeq : Q=AuxTerm.lam B := by injection hQpacked
      subst Q
      obtain ⟨R,hmR,hR⟩ := ih marked hbody B hB
      exact ⟨.lam R,by simp only [finiteMark,hmR,Option.map_some],.lam marked R hR⟩
  | ordinary f base ih =>
    intro r hm Q hQ
    have he : MarkedTerm.marked f (headResult f) base [] .nil=r := Option.some.inj hm
    subst r
    obtain ⟨values,hQpacked,hvalues⟩ := NumberedPositiveMarkProof.ordinaryRepresentation (.ordinary f base) Q hQ f base rfl
    have hQeq : Q=AuxTerm.ordinary f values := by injection hQpacked
    subst Q
    exact ⟨.numbered n f (headResult f) values [] .nil,rfl,
      .numbered f (headResult f) base values [] .nil .nil n (Nat.le_refl _)
        (NumberedPositiveMarkProof.lowerArguments (Nat.le_succ n) base values hvalues) .nil⟩
  | marked f output base types extras ihb ihe => intro r hm Q hQ; cases hm
  | nil => trivial
  | cons q rest ihq ihr => trivial

theorem primitiveMark : NumberedRepresentationRigidityTargets.ActualPrimitiveMark := by
  intro Symbol arity n Gamma tau q r hm Q hQ
  obtain ⟨R,he,hR⟩ := finiteMarkWitness Symbol arity n Gamma tau q r hm Q hQ
  exact ⟨R,.mk n Q R he,hR⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRepresentationRigidityProof
