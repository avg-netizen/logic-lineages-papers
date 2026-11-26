import LogicLineages.PersistentMarking.TwoEnvironmentCases1
import LogicLineages.PersistentMarking.TwoEnvironmentCases2
import LogicLineages.PersistentMarking.TwoEnvironmentCases3
import LogicLineages.PersistentMarking.TwoEnvironmentCases4
import LogicLineages.PersistentMarking.TwoEnvironmentCases5
namespace LogicLineages.PersistentMarking.TwoEnvironmentProof
open Spine NameBridge TwoEnvironmentSupport RefinementSubstitutionSupport
open ExtendedMeasure

theorem step (S : Signature) (n : Nat) (small : Smaller S n) (j : ExtendedJudgment) (h : ExtendedTree S j) (hn : treeSize h = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ j := by
  cases h with
  | var =>
    exact TwoEnvironmentCases.case_var S n small  hn
  | @abs σ s τ t x hp ht hxs hxt hc =>
    exact TwoEnvironmentCases.case_abs S n small hp ht hxs hxt hc hn
  | funHead hp ht heq htype hm =>
    exact TwoEnvironmentCases.case_funHead S n small hp ht heq htype hm hn
  | @put f ss t hp ht hc =>
    exact TwoEnvironmentCases.case_put S n small hp ht hc hn
  | @select f τ ss es t i q domains r hp ht ha hq hcall hc =>
    exact TwoEnvironmentCases.case_select S n small hp ht ha hq hcall hc hn
  | @fabs f σ τ base extras body x hp ht hxo hxb hc =>
    exact TwoEnvironmentCases.case_fabs S n small hp ht hxo hxb hc hn
  | copy hp ht hpref hw =>
    exact TwoEnvironmentCases.case_copy S n small hp ht hpref hw hn
  | stat hp ht heq hm hw =>
    exact TwoEnvironmentCases.case_stat S n small hp ht heq hm hw hn
  | inHead hp ht heq hm ho =>
    exact TwoEnvironmentCases.case_inHead S n small hp ht heq hm ho hn
  | marked1 hp ht hpref hb he =>
    exact TwoEnvironmentCases.case_marked1 S n small hp ht hpref hb he hn
  | marked2 hp ht heq hm hb he =>
    exact TwoEnvironmentCases.case_marked2 S n small hp ht heq hm hb he hn
  | @drop f τ base t extras added hp ht hc =>
    exact TwoEnvironmentCases.case_drop S n small hp ht hc hn
  | @perm f τ base es t ds hp ht hperm hc =>
    exact TwoEnvironmentCases.case_perm S n small hp ht hperm hc hn
  | @copies f τ base extras t ps hp ht hcopies hc =>
    exact TwoEnvironmentCases.case_copies S n small hp ht hcopies hc hn
  | @pselect f τ base extras t i q domains args r hp ht ha hq htuple hcall hc =>
    exact TwoEnvironmentCases.case_pselect S n small hp ht ha hq htuple hcall hc hn
  | strictIntro hp ht hm hc =>
    exact TwoEnvironmentCases.case_strictIntro S n small hp ht hm hc hn
  | matchingNil =>
    exact TwoEnvironmentCases.case_matchingNil S n small  hn
  | matchingCons hr hw hm =>
    exact TwoEnvironmentCases.case_matchingCons S n small hr hw hm hn
  | multisetReplace hs ht hnon hm hc =>
    exact TwoEnvironmentCases.case_multisetReplace S n small hs ht hnon hm hc hn
  | coverageNil =>
    exact TwoEnvironmentCases.case_coverageNil S n small  hn
  | coverageCons ha hc hs =>
    exact TwoEnvironmentCases.case_coverageCons S n small ha hc hs hn
  | wholeNil =>
    exact TwoEnvironmentCases.case_wholeNil S n small  hn
  | @wholeCons f base extras q qs hw hs =>
    exact TwoEnvironmentCases.case_wholeCons S n small hw hs hn
  | orderedNil => exact TwoEnvironmentCases.case_orderedNil S n small hn
  | orderedCons hw hs => exact TwoEnvironmentCases.case_orderedCons S n small hw hs hn
end LogicLineages.PersistentMarking.TwoEnvironmentProof
