module

public import LogicLineages.NativeModule.PersistentMarking.RefinementAppendProof
public import LogicLineages.NativeModule.PersistentMarking.RefinementFreeCallProof
public import LogicLineages.NativeModule.PersistentMarking.RefinementCallMapProof
public import LogicLineages.NativeModule.PersistentMarking.SpineCallTypingProof

@[expose] public section

namespace LogicLineages.PersistentMarking.RefinementFullCallProof
open Spine NameBridge OpeningFoundationProof

theorem lambdaCase (S : Signature) (σ ρ : Ty) (q s a b : Expr) (as bs : Args) (τ : Ty) (r : Expr) (old : Nat)
    (hp : PaperTerm S (.lam σ q) (.arrow σ ρ)) (hs : PaperTerm S (.lam σ s) (.arrow σ ρ))
    (hf : freeOccurs (σ,old) q = false) (hg : freeOccurs (σ,old) s = false)
    (hc : RefinementTree S (openBody σ old q) (openBody σ old s))
    (ha : RefinementTree S a b) (hab : RefinementBasesTree S as bs)
    (hat : Typed EmptyContext a σ) (hbt : Typed EmptyContext b σ)
    (htaila : CallTyped EmptyContext q.type as τ) (htailb : CallTyped EmptyContext s.type bs τ)
    (hr : apply (.lam σ s) (.cons b bs) = some r)
    (ih : ∀ q s as τ r, RefinementTree S q s → RefinementBasesTree S as bs →
      CallTyped EmptyContext q.type as τ → CallTyped EmptyContext s.type bs τ →
      apply s bs = some r → ∃ p, apply q as = some p ∧ Refines S p r) :
    ∃ p, apply (.lam σ q) (.cons a as) = some p ∧ Refines S p r := by
  have hqtype : q.type = ρ := (Ty.arrow.inj (SpineShiftProof.annotationExact _ _ _ hp.1)).2
  have hstype : s.type = ρ := (Ty.arrow.inj (SpineShiftProof.annotationExact _ _ _ hs.1)).2
  let x := max (maxFreeName q) (max (maxFreeName s) (max (maxFreeArgs as) (maxFreeArgs bs))) + 1
  have hxq : freeOccurs (σ,x) q = false := aboveFresh σ x q (by dsimp [x]; omega)
  have hxs : freeOccurs (σ,x) s = false := aboveFresh σ x s (by dsimp [x]; omega)
  have hxa : freeOccursArgs (σ,x) as = false := aboveFreshArgs σ x as (by dsimp [x]; omega)
  have hxb : freeOccursArgs (σ,x) bs = false := aboveFreshArgs σ x bs (by dsimp [x]; omega)
  have hqo := ElementarySupportProof.openingPaper S σ ρ x q hp
  have hso := ElementarySupportProof.openingPaper S σ ρ x s hs
  have hqot := SpineShiftProof.annotationExact _ _ _ hqo.1
  have hsot := SpineShiftProof.annotationExact _ _ _ hso.1
  have harel : Refines S (openBody σ x q) (openBody σ x s) :=
    RefinementFreshOpeningProof.opening S σ q s x ⟨.abs hp hs hf hg hc⟩ hxq hxs
  obtain ⟨hopened⟩ := harel
  have hbtype := SpineShiftProof.annotationExact _ _ _ hbt
  have hrAux : applyAux s bs (.cons b .nil) = some r := by simpa only [apply,applyAux,hbtype,ite_true] using hr
  obtain ⟨r0,hr0⟩ := RefinementFreeCallProof.success s bs (.cons b .nil) (.cons (.free σ x) .nil) r hrAux
  have hrightSym : apply (.lam σ s) (.cons (.free σ x) bs) = some r0 := by
    simpa only [apply,applyAux,Expr.type,ite_true] using hr0
  have hrightOpen : apply (openBody σ x s) bs = some r0 := by
    rw [← RefinementFreeCallProof.call σ x s bs]
    exact hrightSym
  have htao : CallTyped EmptyContext (openBody σ x q).type as τ := by simpa only [hqot,hqtype] using htaila
  have htbo : CallTyped EmptyContext (openBody σ x s).type bs τ := by simpa only [hsot,hstype] using htailb
  obtain ⟨p0,hp0,href⟩ := ih (openBody σ x q) (openBody σ x s) as τ r0 hopened hab htao htbo hrightOpen
  have hleftSym : apply (.lam σ q) (.cons (.free σ x) as) = some p0 := by
    rw [RefinementFreeCallProof.call σ x q as]
    exact hp0
  let γ := RefinementCallMapProof.replace σ x a
  let δ := RefinementCallMapProof.replace σ x b
  have hγ : FreeMapTyped EmptyContext γ := RefinementCallMapProof.typed σ x a hat
  have hδ : FreeMapTyped EmptyContext δ := RefinementCallMapProof.typed σ x b hbt
  have hsymta : CallTyped EmptyContext (.arrow σ ρ) (.cons (.free σ x) as) τ := .cons .free (by simpa only [hqtype] using htaila)
  have hsymtb : CallTyped EmptyContext (.arrow σ ρ) (.cons (.free σ x) bs) τ := .cons .free (by simpa only [hstype] using htailb)
  have hleft := FreeCallProof.successfulCallCovariance EmptyContext γ (.lam σ q) (.arrow σ ρ) _ τ p0 hγ hp.1 hsymta hleftSym
  have hright := FreeCallProof.successfulCallCovariance EmptyContext δ (.lam σ s) (.arrow σ ρ) _ τ r0 hδ hs.1 hsymtb hrightSym
  rw [RefinementCallMapProof.absent σ x a 0 (.lam σ q) hxq,RefinementCallMapProof.realize σ x a as hxa] at hleft
  rw [RefinementCallMapProof.absent σ x b 0 (.lam σ s) hxs,RefinementCallMapProof.realize σ x b bs hxb] at hright
  have heq : freeSub δ 0 r0 = r := Option.some.inj (hright.symm.trans hr)
  refine ⟨freeSub γ 0 p0,hleft,?_⟩
  rw [← heq]
  exact RefinementSubstitutionProof.freeSubstitution S γ δ p0 r0 hγ hδ (RefinementCallMapProof.related S σ x a b ⟨ha⟩) href

theorem call (S : Signature) (n : Nat) : ∀ (q s : Expr) (as bs : Args) (τ : Ty) (r : Expr),
    RefinementTree S q s → RefinementBasesTree S as bs →
    CallTyped EmptyContext q.type as τ → CallTyped EmptyContext s.type bs τ →
    apply s bs = some r → sizeOf bs = n → ∃ p, apply q as = some p ∧ Refines S p r := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro q s as bs τ r h hab hta htb hr hn
    cases bs with
    | nil =>
      cases hab
      simp only [apply,Option.some.injEq] at hr
      subst r
      exact ⟨q,rfl,⟨h⟩⟩
    | cons b bs =>
      cases hab with
      | @cons a _ as _ ha hab =>
        cases h with
        | var => simp [apply,applyAux] at hr
        | @head f qb sb hp hs hb =>
          have hca := SpineCallTypingProof.consumeExact _ _ _ _ hta
          have hcb := SpineCallTypingProof.consumeExact _ _ _ _ htb
          simp only [Expr.type] at hca hcb
          have hright : apply (.head f sb) (.cons b bs) = some (.marked f τ sb (.cons b bs)) := by
            simpa only [apply,applyAux,SubstitutionProof.emptyArgsSubstitution,hcb,Option.map_some]
          have heq := Option.some.inj (hright.symm.trans hr)
          subst r
          refine ⟨.marked f τ qb (.cons a as),?_,?_⟩
          · simpa only [apply,applyAux,SubstitutionProof.emptyArgsSubstitution,hca,Option.map_some]
          · exact RefinementAppendProof.headAppend S f τ qb sb _ _ ⟨.head hp hs hb⟩ ⟨.cons ha hab⟩
        | @marked f σ qb qe sb se hp hs hb he =>
          have hca := SpineCallTypingProof.consumeExact _ _ _ _ hta
          have hcb := SpineCallTypingProof.consumeExact _ _ _ _ htb
          simp only [Expr.type] at hca hcb
          have hright : apply (.marked f σ sb se) (.cons b bs) = some (.marked f τ sb (se.append (.cons b bs))) := by
            simpa only [apply,applyAux,SubstitutionProof.emptyArgsSubstitution,hcb,Option.map_some]
          have heq := Option.some.inj (hright.symm.trans hr)
          subst r
          refine ⟨.marked f τ qb (qe.append (.cons a as)),?_,?_⟩
          · simpa only [apply,applyAux,SubstitutionProof.emptyArgsSubstitution,hca,Option.map_some]
          · exact RefinementAppendProof.markedAppend S f σ τ qb qe sb se _ _ ⟨.marked hp hs hb he⟩ ⟨.cons ha hab⟩
        | @abs σ q ρ s old hp hs hf hg hc =>
          cases hta with
          | cons hat htaila =>
            cases htb with
            | cons hbt htailb =>
              exact lambdaCase S σ ρ q s a b as bs τ r old hp hs hf hg hc ha hab hat hbt htaila htailb hr
                (fun q s as τ r h hab hta htb hr => ih (sizeOf bs) (by change 1 + sizeOf b + sizeOf bs = n at hn; omega) q s as bs τ r h hab hta htb hr rfl)


theorem fullApplication : RefinementSyntaxTargets.FullApplication := by
  intro S q s as bs τ r h hab hta htb hr
  obtain ⟨h⟩ := h
  obtain ⟨hab⟩ := hab
  exact call S (sizeOf bs) q s as bs τ r h hab hta htb hr rfl
end LogicLineages.PersistentMarking.RefinementFullCallProof
