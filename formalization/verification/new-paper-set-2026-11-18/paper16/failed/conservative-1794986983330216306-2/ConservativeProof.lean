import LogicLineages.PersistentMarking.ConservativeBinderProof
import LogicLineages.PersistentMarking.RefinementMarkProof
namespace LogicLineages.PersistentMarking.ConservativeProof
open Spine NameBridge ConservativeResults ConservativeListSupport ConservativeOwnerSupport
open ExtendedMeasure

theorem prove (S : Signature) (n : Nat) : ∀ j (h : ExtendedTree S j), treeSize h = n → Result S j := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro j h hn
    have small : Smaller S n := by
      intro j h hlt
      exact ih (treeSize h) hlt j h rfl
    cases h with
    | var =>
      intro q hq ho
      cases hq
      exact .var
    | @abs σ s τ t x hp ht hxs hxt hc =>
      simp only [treeSize] at hn
      exact ConservativeBinderProof.abstraction S n small σ τ s t x hp ht hxs hxt hc (by omega)
    | funHead hp ht heq htype hm =>
      simp only [treeSize] at hn
      intro q hq ho
      cases hq with
      | head hqp hsp hb =>
        exact .funHead hqp ht heq htype (small _ hm (by omega) _ hb ho)
    | @put f ss t hp ht hc =>
      simp only [treeSize] at hn
      intro q hq ho
      cases hq with
      | @head _ qs _ hqp hsp hb =>
        obtain ⟨r,hm,href⟩ := RefinementMarkProof.refinementMarkReflection S _ _ _ ⟨.head hqp hsp hb⟩ rfl
        simp only [Spine.mark,Option.some.injEq] at hm
        subst r
        obtain ⟨hr⟩ := href
        exact .put hqp ht (small _ hc (by omega) _ hr ho)
    | @select f τ ss es t i q domains r hp ht ha hq hcall hc =>
      simp only [treeSize] at hn
      intro p href ho
      cases href with
      | @marked _ _ qb qe _ _ hpp hps hb he =>
        exact ConservativeSelectionProof.selectCase S f τ ss es qb qe t q r domains (ownerCopies f ss es domains) hp ht (.marked hpp hps hb he) ha hq (wholeTuple f ss es domains) hcall
          (fun p hr => by obtain ⟨hr⟩ := hr; exact small _ hc (by omega) p hr ho)
    | @fabs f σ τ base extras body x hp ht hxo hxb hc =>
      simp only [treeSize] at hn
      exact ConservativeBinderProof.functional S n small f σ τ base extras body x hp ht hxo hxb hc (by omega)
    | copy hp ht hpref hw =>
      simp only [treeSize] at hn
      intro q hq ho
      cases hq with
      | marked hqp hsp hb he =>
        exact .copy hqp ht hpref (small _ hw (by omega) _ _ _ (.marked hqp hsp hb he) ho)
    | stat hp ht heq hm hw =>
      simp only [treeSize] at hn
      intro q hq ho
      cases hq with
      | marked hqp hsp hb he =>
        exact .stat hqp ht heq (small _ hm (by omega) _ hb ho) (small _ hw (by omega) _ _ _ (.marked hqp hsp hb he) ho)
    | inHead hp ht heq hm ho =>
      intro q hq hordinary
      exact False.elim hordinary
    | marked1 hp ht hpref hb he =>
      intro q hq ho
      exact False.elim ho
    | marked2 hp ht heq hm hb he =>
      intro q hq ho
      exact False.elim ho
    | @drop f τ base t extras added hp ht hc =>
      simp only [treeSize] at hn
      intro q hq ho
      have howner := OwnerRefinementProof.prefixOmission S f τ base (extras.append added) extras hp (prefixAppend extras added)
      obtain ⟨hcomp⟩ := RefinementTransitivityProof.transitive S _ _ _ ⟨hq⟩ howner
      exact small _ hc (by omega) q hcomp ho
    | @perm f τ base es t ds hp ht hperm hc =>
      simp only [treeSize] at hn
      intro q hq ho
      have howner := OwnerRefinementProof.permutation S f τ base es ds hp hperm
      obtain ⟨hcomp⟩ := RefinementTransitivityProof.transitive S _ _ _ ⟨hq⟩ howner
      exact small _ hc (by omega) q hcomp ho
    | @copies f τ base extras t ps hp ht hcopies hc =>
      simp only [treeSize] at hn
      intro q hq ho
      have howner := OwnerRefinementProof.prefixExpansion S f τ base extras ps hp hcopies
      obtain ⟨hcomp⟩ := RefinementTransitivityProof.transitive S _ _ _ ⟨hq⟩ howner
      exact small _ hc (by omega) q hcomp ho
    | @pselect f τ base extras t i q domains args r hp ht ha hq htuple hcall hc =>
      simp only [treeSize] at hn
      intro p href ho
      cases href with
      | @marked _ _ qb qe _ _ hpp hps hb he =>
        exact ConservativeSelectionProof.selectCase S f τ base extras qb qe t q r domains args hp ht (.marked hpp hps hb he) ha hq htuple hcall
          (fun p hr => by obtain ⟨hr⟩ := hr; exact small _ hc (by omega) p hr ho)
    | strictIntro hp ht hm hc =>
      simp only [treeSize] at hn
      intro q hq ho
      obtain ⟨r,hmq,href⟩ := RefinementMarkProof.refinementMarkReflection S _ _ _ ⟨hq⟩ hm
      obtain ⟨href⟩ := href
      exact .intro (refiningPaper hq hp) ht hmq (small _ hc (by omega) r href ho)
    | matchingNil =>
      intro qs hq ho
      cases hq
      exact .nil
    | matchingCons hr hw hm =>
      simp only [treeSize] at hn
      intro qs hq ho
      have hot := removeOrdinaryParts hr ho
      cases hq with
      | cons h hs => exact .cons hr (small _ hw (by omega) _ h hot.1) (small _ hm (by omega) _ hs hot.2)
    | multisetReplace hs ht hnon hm hc =>
      simp only [treeSize] at hn
      intro qs hq ho
      obtain ⟨qk,qr,hsp,hk,hr⟩ := transportSplit hq hs
      obtain ⟨hk⟩ := hk
      obtain ⟨hr⟩ := hr
      have hot := splitOrdinary ht ho
      exact .replace hsp ht (baseNonempty hr hnon) (small _ hm (by omega) qk hk hot.1) (small _ hc (by omega) qr hr hot.2)
    | coverageNil =>
      intro qs hq ho
      exact .nil
    | coverageCons ha hc hs =>
      simp only [treeSize] at hn
      intro qs hq ho
      obtain ⟨q,hat,href⟩ := baseAt hq ha
      obtain ⟨href⟩ := href
      exact .cons hat (small _ hc (by omega) q href ho.1) (small _ hs (by omega) qs hq ho.2)
    | wholeNil =>
      intro qb qe τ href ho
      exact .nil
    | @wholeCons f base extras q qs hw hs =>
      simp only [treeSize] at hn
      intro qb qe τ href ho
      have hrt := RefinementTransitivitySupport.retype q.type href
      exact .cons (small _ hw (by omega) _ hrt ho.1) (small _ hs (by omega) qb qe τ href ho.2)
    | orderedNil => trivial
    | orderedCons _ _ => trivial

theorem weak : ConservativeTargets.Weak := by
  intro S q s t href he ho
  obtain ⟨href⟩ := href
  obtain ⟨he⟩ := he
  exact prove S (treeSize he) _ he rfl q href ho

theorem strict : ConservativeTargets.Strict := by
  intro S q s t href he ho
  obtain ⟨href⟩ := href
  obtain ⟨he⟩ := he
  exact prove S (treeSize he) _ he rfl q href ho

theorem matching : ConservativeTargets.Matching := by
  intro S qs ss ts href he ho
  obtain ⟨href⟩ := href
  obtain ⟨he⟩ := he
  exact prove S (treeSize he) _ he rfl qs href ho

theorem multiset : ConservativeTargets.Multiset := by
  intro S qs ss ts href he ho
  obtain ⟨href⟩ := href
  obtain ⟨he⟩ := he
  exact prove S (treeSize he) _ he rfl qs href ho

theorem coverage : ConservativeTargets.Coverage := by
  intro S qs ss ts href he ho
  obtain ⟨href⟩ := href
  obtain ⟨he⟩ := he
  exact prove S (treeSize he) _ he rfl qs href ho

theorem fullConservative : ConservativeTargets.FullConservative := ⟨weak,strict,matching,multiset,coverage⟩
end LogicLineages.PersistentMarking.ConservativeProof
