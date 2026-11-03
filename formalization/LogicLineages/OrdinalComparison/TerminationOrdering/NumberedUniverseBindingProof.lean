module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseBindingTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseBindingProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedUniverseBindingTargets

theorem renameGood {Symbol : Type} {arity : Symbol → Nat} (K : Ty → Prop) (H : Head Symbol → Prop)
    {Gamma : List Ty} {tau : Ty} (q : AuxTerm Symbol arity Gamma tau) :
    ∀ (Delta : List Ty) (rho : Renaming Gamma Delta), Good K H q → Good K H (NumberedRewriteSyntax.rename q rho) := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => ∀ (Delta : List Ty) (rho : Renaming Gamma Delta),
      GoodArguments K H args → GoodArguments K H (NumberedRewriteSyntax.renameArguments args rho))
  case var v => intro Delta rho h; exact h
  case lam body ih =>
    intro Delta rho h
    have hb := ih _ rho.lift ⟨h.1.2.2,h.2⟩
    exact ⟨⟨h.1.1,h.1.2.1,hb.1⟩,hb.2⟩
  case app q a ihq iha =>
    intro Delta rho h
    have hq := ihq _ rho ⟨h.1.2.1,h.2.1⟩
    have ha := iha _ rho ⟨h.1.2.2,h.2.2⟩
    exact ⟨⟨h.1.1,hq.1,ha.1⟩,hq.2,ha.2⟩
  case bottom tau => intro Delta rho h; exact h
  case ordinary f base ih =>
    intro Delta rho h
    have hb := ih _ rho ⟨h.1.2,h.2.2⟩
    exact ⟨⟨h.1.1,hb.1⟩,h.2.1,hb.2⟩
  case numbered k f tau base types extras ihb ihe =>
    intro Delta rho h
    have hb := ihb _ rho ⟨h.1.2.1,h.2.2.1⟩
    have he := ihe _ rho ⟨h.1.2.2,h.2.2.2⟩
    exact ⟨⟨h.1.1,hb.1,he.1⟩,h.2.1,hb.2,he.2⟩
  case nil => intros; exact ⟨trivial,trivial⟩
  case cons Gamma sigma types q rest ihq ihr Delta rho h =>
    have hq := ihq _ rho ⟨h.1.1,h.2.1⟩
    have hr := ihr _ rho ⟨h.1.2,h.2.2⟩
    exact ⟨⟨hq.1,hr.1⟩,hq.2,hr.2⟩

theorem actualRenaming : ActualRenaming := by
  intro Symbol arity K H Gamma Delta tau q rho h
  exact renameGood K H q Delta rho h

theorem actualArgumentRenaming : ActualArgumentRenaming := by
  intro Symbol arity K H Gamma Delta types args rho h
  induction types with
  | nil => cases args; exact ⟨trivial,trivial⟩
  | cons tau types ih => cases args with
    | cons q rest =>
      have hq := renameGood K H q Delta rho ⟨h.1.1,h.2.1⟩
      have hr := ih rest ⟨h.1.2,h.2.2⟩
      exact ⟨⟨hq.1,hr.1⟩,hq.2,hr.2⟩

theorem liftGood {Symbol : Type} {arity : Symbol → Nat} (K : Ty → Prop) (H : Head Symbol → Prop)
    {Gamma Delta : List Ty} {sigma : Ty} (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (h : GoodSubstitution K H rho) : GoodSubstitution K H (liftSubstitution (sigma:=sigma) rho) := by
  intro tau v ht
  cases v with
  | here => exact ⟨ht,trivial⟩
  | there v => exact renameGood K H (rho v) _ (Renaming.weaken Delta sigma) (h v ht)

theorem substituteGood {Symbol : Type} {arity : Symbol → Nat} (K : Ty → Prop) (H : Head Symbol → Prop)
    {Gamma : List Ty} {tau : Ty} (q : AuxTerm Symbol arity Gamma tau) :
    ∀ (Delta : List Ty) (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
      Good K H q → GoodSubstitution K H rho → Good K H (NumberedRewriteSyntax.substitute q rho) := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => ∀ (Delta : List Ty) (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
      GoodArguments K H args → GoodSubstitution K H rho → GoodArguments K H (NumberedRewriteSyntax.substituteArguments args rho))
  case var v => intro Delta rho h hr; exact hr v h.1
  case lam body ih =>
    intro Delta rho h hr
    have hb := ih _ (liftSubstitution rho) ⟨h.1.2.2,h.2⟩ (liftGood K H rho hr)
    exact ⟨⟨h.1.1,h.1.2.1,hb.1⟩,hb.2⟩
  case app q a ihq iha =>
    intro Delta rho h hr
    have hq := ihq _ rho ⟨h.1.2.1,h.2.1⟩ hr
    have ha := iha _ rho ⟨h.1.2.2,h.2.2⟩ hr
    exact ⟨⟨h.1.1,hq.1,ha.1⟩,hq.2,ha.2⟩
  case bottom tau => intro Delta rho h hr; exact h
  case ordinary f base ih =>
    intro Delta rho h hr
    have hb := ih _ rho ⟨h.1.2,h.2.2⟩ hr
    exact ⟨⟨h.1.1,hb.1⟩,h.2.1,hb.2⟩
  case numbered k f tau base types extras ihb ihe =>
    intro Delta rho h hr
    have hb := ihb _ rho ⟨h.1.2.1,h.2.2.1⟩ hr
    have he := ihe _ rho ⟨h.1.2.2,h.2.2.2⟩ hr
    exact ⟨⟨h.1.1,hb.1,he.1⟩,h.2.1,hb.2,he.2⟩
  case nil => intros; exact ⟨trivial,trivial⟩
  case cons Gamma sigma types q rest ihq ihr Delta rho h hr =>
    have hq := ihq _ rho ⟨h.1.1,h.2.1⟩ hr
    have ht := ihr _ rho ⟨h.1.2,h.2.2⟩ hr
    exact ⟨⟨hq.1,ht.1⟩,hq.2,ht.2⟩

theorem actualSubstitution : ActualSubstitution := by
  intro Symbol arity K H Gamma Delta tau q rho h hr
  exact substituteGood K H q Delta rho h hr

theorem actualArgumentSubstitution : ActualArgumentSubstitution := by
  intro Symbol arity K H Gamma Delta types args rho h hr
  induction types with
  | nil => cases args; exact ⟨trivial,trivial⟩
  | cons tau types ih => cases args with
    | cons q rest =>
      have hq := substituteGood K H q Delta rho ⟨h.1.1,h.2.1⟩ hr
      have ht := ih rest ⟨h.1.2,h.2.2⟩
      exact ⟨⟨hq.1,ht.1⟩,hq.2,ht.2⟩

theorem markGood {Symbol : Type} {arity : Symbol → Nat} (K : Ty → Prop) (H : Head Symbol → Prop)
    (n : Nat) {Gamma : List Ty} {tau : Ty} (q : AuxTerm Symbol arity Gamma tau) :
    ∀ r, finiteMark n q=some r → Good K H q → Good K H r := by
  induction q using AuxTerm.rec (motive_2 := fun _ _ _ => True)
  case var v => intro r he; cases he
  case lam body ih =>
    intro r he h
    simp only [finiteMark,Option.map_eq_some_iff] at he
    obtain ⟨b,hb,rfl⟩ := he
    have hi := ih b hb ⟨h.1.2.2,h.2⟩
    exact ⟨⟨h.1.1,h.1.2.1,hi.1⟩,hi.2⟩
  case app q a ihq iha => intro r he; cases he
  case bottom tau => intro r he; cases he
  case ordinary f base ih =>
    intro r he h
    cases he
    exact ⟨⟨h.1.1,h.1.2,trivial⟩,h.2.1,h.2.2,trivial⟩
  case numbered k f tau base types extras ihb ihe => intro r he; cases he
  case nil => trivial
  case cons => trivial

theorem actualFiniteMark : ActualFiniteMark := by
  intro Symbol arity K H n Gamma tau q r he h
  exact markGood K H n q r he h

theorem actualBeta : ActualBeta := by
  intro Symbol arity K H Gamma sigma tau body a hb ha
  apply substituteGood K H body Gamma (singleSubstitution a) hb
  intro upsilon v ht
  cases v with
  | here => exact ha
  | there v => exact ⟨ht,trivial⟩

theorem appendGood {Symbol : Type} {arity : Symbol → Nat} (K : Ty → Prop) (H : Head Symbol → Prop)
    {Gamma xs ys : List Ty} (a : AuxArguments Symbol arity Gamma xs) (b : AuxArguments Symbol arity Gamma ys)
    (ha : GoodArguments K H a) (hb : GoodArguments K H b) :
    GoodArguments K H (NumberedRewriteSyntax.appendArguments a b) := by
  induction xs with
  | nil => cases a; exact hb
  | cons tau xs ih => cases a with
    | cons q rest =>
      have hr := ih rest ⟨ha.1.2,ha.2.2⟩
      exact ⟨⟨ha.1.1,hr.1⟩,ha.2.1,hr.2⟩

theorem actualOpenedNumbered : ActualOpenedNumbered := by
  intro Symbol arity K H hc n k Gamma f sigma tau base types extras h
  have hs : K sigma := hc (.arrow sigma tau) h.1.1 sigma (by simp [Ty.subtypes,NumberedFiniteUniverseProof.subtypeSelf])
  have ht : K tau := hc (.arrow sigma tau) h.1.1 tau (by simp [Ty.subtypes,NumberedFiniteUniverseProof.subtypeSelf])
  have hb := actualArgumentRenaming Symbol arity K H Gamma (sigma::Gamma) _ base (Renaming.weaken Gamma sigma) ⟨h.1.2.1,h.2.2.1⟩
  have he := actualArgumentRenaming Symbol arity K H Gamma (sigma::Gamma) _ extras (Renaming.weaken Gamma sigma) ⟨h.1.2.2,h.2.2.2⟩
  have hv : GoodArguments K H (AuxArguments.cons (AuxTerm.var .here) .nil : AuxArguments Symbol arity (sigma::Gamma) [sigma]) := by
    exact ⟨⟨hs,trivial⟩,trivial,trivial⟩
  have he' := appendGood K H _ _ he hv
  exact ⟨⟨ht,hb.1,he'.1⟩,h.2.1,hb.2,he'.2⟩

theorem actualSelfArguments : ActualSelfArguments := by
  intro Symbol arity K H n Gamma f base extraTypes extras types hf hb he ht
  induction types with
  | nil => exact ⟨trivial,trivial⟩
  | cons tau types ih =>
    have hq : Good K H (AuxTerm.numbered n f tau base extraTypes extras) :=
      ⟨⟨ht tau (by simp),hb.1,he.1⟩,hf,hb.2,he.2⟩
    have hr := ih (fun t hm => ht t (by simp [hm]))
    exact ⟨⟨hq.1,hr.1⟩,hq.2,hr.2⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseBindingProof
