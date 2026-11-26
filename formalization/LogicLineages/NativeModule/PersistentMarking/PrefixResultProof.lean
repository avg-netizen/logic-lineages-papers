module

public import LogicLineages.NativeModule.PersistentMarking.PrefixEscapeSupportTargets
public import LogicLineages.NativeModule.PersistentMarking.OwnerRefinementProof

@[expose] public section

namespace LogicLineages.PersistentMarking.PrefixResultProof
open Spine AuxiliaryReflexivityProof RefinementAppendProof OwnerOccurrenceProof

theorem prefixResult : PrefixEscapeSupportTargets.PrefixResult := by
  intro S f ρ τ base extras pref added hp hprefix hadded
  have hpτ := retypePaper S f ρ τ base extras hp
  have hc := OwnerRefinementProof.copiesExtras S f τ base extras added hpτ hadded
  cases hpτ.1 with
  | marked hb he =>
    have hf := prefixFacts hprefix he hpτ.2.2.2
    have hpref : PaperTerm S (.marked f τ base pref) τ := ⟨.marked hb hf.1,hpτ.2.1,hpτ.2.2.1,hf.2⟩
    have hout := appendPaper S f τ τ base pref added hpref hc.1 hc.2.1
    obtain ⟨hbase⟩ := refinementBasesRefl S base _ hb hpτ.2.2.1
    obtain ⟨hprev⟩ := refinementExtrasRefl S f base extras pref hf.1 hf.2 (fun i q h => ⟨i,prefixMember hprefix h⟩)
    obtain ⟨hnew⟩ := hc.2.2
    obtain ⟨hall⟩ := appendWitness hprev hnew
    exact ⟨.marked hpτ hout hbase hall⟩
end LogicLineages.PersistentMarking.PrefixResultProof
