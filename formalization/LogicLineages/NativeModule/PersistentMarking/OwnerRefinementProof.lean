module

public import LogicLineages.NativeModule.PersistentMarking.OwnerOccurrenceProof

@[expose] public section

namespace LogicLineages.PersistentMarking.OwnerRefinementProof
open Spine AuxiliaryReflexivityProof RefinementAppendProof OwnerOccurrenceProof

theorem prefixOmission : OwnerRefinementTargets.PrefixOmission := by
  intro S f τ base extras pref hp hprefix
  cases hp.1 with
  | marked hb he =>
    have hf := prefixFacts hprefix he hp.2.2.2
    have ht : PaperTerm S (.marked f τ base pref) τ := ⟨.marked hb hf.1,hp.2.1,hp.2.2.1,hf.2⟩
    obtain ⟨hbase⟩ := refinementBasesRefl S base _ hb hp.2.2.1
    obtain ⟨hextras⟩ := refinementExtrasRefl S f base extras pref hf.1 hf.2 (fun i q h => ⟨i,prefixMember hprefix h⟩)
    exact ⟨.marked hp ht hbase hextras⟩

theorem permutation : OwnerRefinementTargets.Permutation := by
  intro S f τ base extras ds hp hperm
  cases hp.1 with
  | marked hb he =>
    have hf := permutationFacts hperm he hp.2.2.2
    have ht : PaperTerm S (.marked f τ base ds) τ := ⟨.marked hb hf.1,hp.2.1,hp.2.2.1,hf.2⟩
    obtain ⟨hbase⟩ := refinementBasesRefl S base _ hb hp.2.2.1
    obtain ⟨hextras⟩ := refinementExtrasRefl S f base extras ds hf.1 hf.2 (fun _ _ h => permutationMember hperm h)
    exact ⟨.marked hp ht hbase hextras⟩

theorem copyRefines (S : Signature) (f : Head) (ρ σ : Ty) (base extras : Args) (q : Expr)
    (hp : PaperTerm S (.marked f ρ base extras) ρ) (hc : PrefixCopy f base extras σ q) :
    Refines S (.marked f σ base extras) q := by
  cases hc with
  | intro hprefix => exact prefixOmission S f σ base extras _ (retypePaper S f ρ σ base extras hp) hprefix

theorem copiesExtras (S : Signature) (f : Head) (τ : Ty) (base extras ps : Args)
    (hp : PaperTerm S (.marked f τ base extras) τ) (h : PrefixCopies f base extras ps) :
    ExtrasTyped EmptyContext ps ∧ ValidArgs S ps ∧ _root_.Nonempty (RefinementExtrasTree S f base extras ps) := by
  induction h with
  | nil => exact ⟨.nil,True.intro,⟨.nil⟩⟩
  | @cons q qs hc hs ih =>
    obtain ⟨hroot⟩ := copyRefines S f τ q.type base extras q hp hc
    have htarget := (RefinementSubstitutionSupport.endpoints hroot).2
    obtain ⟨htail⟩ := ih.2.2
    exact ⟨.cons htarget.1 ih.1,⟨htarget.2,ih.2.1⟩,⟨.cons (.owner hroot) htail⟩⟩

theorem prefixExpansion : OwnerRefinementTargets.PrefixExpansion := by
  intro S f τ base extras ps hp hcopies
  have hf := copiesExtras S f τ base extras ps hp hcopies
  have hnew := appendPaper S f τ τ base extras ps hp hf.1 hf.2.1
  cases hp.1 with
  | marked hb he =>
    obtain ⟨hbase⟩ := refinementBasesRefl S base _ hb hp.2.2.1
    obtain ⟨hold⟩ := refinementExtrasRefl S f base extras extras he hp.2.2.2 (fun i q h => ⟨i,h⟩)
    obtain ⟨hcopies⟩ := hf.2.2
    obtain ⟨hall⟩ := appendWitness hold hcopies
    exact ⟨.marked hp hnew hbase hall⟩

theorem refinedCopies : OwnerRefinementTargets.RefinedCopies := by
  intro S f τ qb qe sb se domains bs href htuple
  obtain ⟨h⟩ := href
  have hp := (RefinementSubstitutionSupport.endpoints h).2
  induction htuple with
  | nil => exact ⟨.nil⟩
  | @cons σ q types qs hc hs ih =>
    cases hc with
    | @intro pref σ hprefix =>
      have hrt := refinementRetyping S f τ σ qb qe sb se ⟨h⟩
      have homit := prefixOmission S f σ sb se pref (retypePaper S f τ σ sb se hp) hprefix
      obtain ⟨hchild⟩ := RefinementTransitivityProof.transitive S _ _ _ hrt homit
      obtain ⟨htail⟩ := ih
      exact ⟨.cons hchild htail⟩
end LogicLineages.PersistentMarking.OwnerRefinementProof
