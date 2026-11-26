import LogicLineages.PersistentMarking.ConservativeCases1
import LogicLineages.PersistentMarking.ConservativeCases2
import LogicLineages.PersistentMarking.ConservativeCases3
import LogicLineages.PersistentMarking.ConservativeCases4
import LogicLineages.PersistentMarking.ConservativeCases5
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
      simp only [treeSize] at hn
      exact ConservativeCases.case_var S n small  hn
    | @abs σ s τ t x hp ht hxs hxt hc =>
      simp only [treeSize] at hn
      exact ConservativeCases.case_abs S n small hp ht hxs hxt hc hn
    | funHead hp ht heq htype hm =>
      simp only [treeSize] at hn
      exact ConservativeCases.case_funHead S n small hp ht heq htype hm hn
    | @put f ss t hp ht hc =>
      simp only [treeSize] at hn
      exact ConservativeCases.case_put S n small hp ht hc hn
    | @select f τ ss es t i q domains r hp ht ha hq hcall hc =>
      simp only [treeSize] at hn
      exact ConservativeCases.case_select S n small hp ht ha hq hcall hc hn
    | @fabs f σ τ base extras body x hp ht hxo hxb hc =>
      simp only [treeSize] at hn
      exact ConservativeCases.case_fabs S n small hp ht hxo hxb hc hn
    | copy hp ht hpref hw =>
      simp only [treeSize] at hn
      exact ConservativeCases.case_copy S n small hp ht hpref hw hn
    | stat hp ht heq hm hw =>
      simp only [treeSize] at hn
      exact ConservativeCases.case_stat S n small hp ht heq hm hw hn
    | inHead hp ht heq hm ho =>
      simp only [treeSize] at hn
      exact ConservativeCases.case_inHead S n small hp ht heq hm ho hn
    | marked1 hp ht hpref hb he =>
      simp only [treeSize] at hn
      exact ConservativeCases.case_marked1 S n small hp ht hpref hb he hn
    | marked2 hp ht heq hm hb he =>
      simp only [treeSize] at hn
      exact ConservativeCases.case_marked2 S n small hp ht heq hm hb he hn
    | @drop f τ base t extras added hp ht hc =>
      simp only [treeSize] at hn
      exact ConservativeCases.case_drop S n small hp ht hc hn
    | @perm f τ base es t ds hp ht hperm hc =>
      simp only [treeSize] at hn
      exact ConservativeCases.case_perm S n small hp ht hperm hc hn
    | @copies f τ base extras t ps hp ht hcopies hc =>
      simp only [treeSize] at hn
      exact ConservativeCases.case_copies S n small hp ht hcopies hc hn
    | @pselect f τ base extras t i q domains args r hp ht ha hq htuple hcall hc =>
      simp only [treeSize] at hn
      exact ConservativeCases.case_pselect S n small hp ht ha hq htuple hcall hc hn
    | strictIntro hp ht hm hc =>
      simp only [treeSize] at hn
      exact ConservativeCases.case_strictIntro S n small hp ht hm hc hn
    | matchingNil =>
      simp only [treeSize] at hn
      exact ConservativeCases.case_matchingNil S n small  hn
    | matchingCons hr hw hm =>
      simp only [treeSize] at hn
      exact ConservativeCases.case_matchingCons S n small hr hw hm hn
    | multisetReplace hs ht hnon hm hc =>
      simp only [treeSize] at hn
      exact ConservativeCases.case_multisetReplace S n small hs ht hnon hm hc hn
    | coverageNil =>
      simp only [treeSize] at hn
      exact ConservativeCases.case_coverageNil S n small  hn
    | coverageCons ha hc hs =>
      simp only [treeSize] at hn
      exact ConservativeCases.case_coverageCons S n small ha hc hs hn
    | wholeNil =>
      simp only [treeSize] at hn
      exact ConservativeCases.case_wholeNil S n small  hn
    | @wholeCons f base extras q qs hw hs =>
      simp only [treeSize] at hn
      exact ConservativeCases.case_wholeCons S n small hw hs hn
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
