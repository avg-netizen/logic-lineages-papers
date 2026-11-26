import LogicLineages.PersistentMarking.ExtraCompressionSupport
namespace LogicLineages.PersistentMarking.ExtraCompressionProof
open Spine ExtraCompressionSupport RefinementAppendProof

theorem extraCompression : ExtraCompressionTargets.ExtraCompression := by
  intro S f g τ base extras targetBase targetExtras hp ht heq hmatching hwhole
  obtain ⟨hm⟩ := hmatching
  obtain ⟨hw⟩ := hwhole
  let ps := copies f base extras targetExtras
  have hps := copiesPrefix f base extras targetExtras
  have hp0 : PaperTerm S (.marked f τ base ps) τ := copiesPaper S f τ base extras targetExtras hp
  obtain ⟨ho⟩ := ordered hw
  have hin : ExtendedWeakTree S (.marked f τ base ps) (.marked g τ targetBase targetExtras) :=
    .inHead hp0 ht heq hm ho
  have he : ExtrasTyped EmptyContext extras := by cases hp.1 with | marked _ he => exact he
  have hp1 : PaperTerm S (.marked f τ base (ps.append extras)) τ :=
    appendPaper S f τ τ base ps extras hp0 he hp.2.2.2
  have hdrop : ExtendedWeakTree S (.marked f τ base (ps.append extras)) (.marked g τ targetBase targetExtras) :=
    .drop hp1 ht hin
  have hf := OwnerRefinementProof.copiesExtras S f τ base extras ps hp hps
  have hp2 : PaperTerm S (.marked f τ base (extras.append ps)) τ :=
    appendPaper S f τ τ base extras ps hp hf.1 hf.2.1
  have hperm : ExtendedWeakTree S (.marked f τ base (extras.append ps)) (.marked g τ targetBase targetExtras) :=
    .perm hp2 ht (permutationBlocks extras ps) hdrop
  exact ⟨.copies hp ht hps hperm⟩
end LogicLineages.PersistentMarking.ExtraCompressionProof
