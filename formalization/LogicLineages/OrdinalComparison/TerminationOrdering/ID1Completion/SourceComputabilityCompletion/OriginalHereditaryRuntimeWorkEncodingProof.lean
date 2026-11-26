module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionDeletionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkEncodingProof
open OriginalHereditaryRuntimeWork OriginalHereditaryAgendaDefinitions
open OriginalHereditaryAnnotatedExpansion (decoratedValue)
open NumberedLeastCodeRepresentative

def indexed (start role typ raw : Nat) : List Nat → List Nat
 | [] => []
 | x :: xs => decoratedValue start role typ raw x :: indexed (start+1) role typ raw xs

theorem indexedRange (start role typ raw : Nat) (xs : List Nat) :
    indexed start role typ raw xs = (List.range xs.length).map
      (fun k => decoratedValue (start+k) role typ raw (xs[k]?.getD 0)) := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih =>
    rw [indexed,List.length_cons,OriginalHereditaryExpansionDeletionProof.rangeFront,List.map_cons,List.map_map]
    simp only [Nat.add_zero]
    congr 1
    rw [ih]
    apply List.map_congr_left
    intro k hk
    simp only [Function.comp_apply,List.getElem?_cons_succ]
    congr 1
    omega

theorem childEncoding {n : Nat} (c : Nat) (a : Job n) (index : Nat)
    (s : OriginalHereditaryWorkBound.State (Fin n)) :
    jobNumber c (child c a index s) = decoratedValue index a.role a.typ
      (codeNumber a.core.code) (OriginalHereditaryExpansion.jobNumber c s) := by
  simp only [jobNumber,child,decoratedValue,OriginalHereditaryAnnotatedExpansion.jobNumber,Nat.unpair_pair]

theorem decorateEncoding {n : Nat} (c : Nat) (a : Job n) (index : Nat)
    (ss : List (OriginalHereditaryWorkBound.State (Fin n))) :
    (decorate c a index ss).map (jobNumber c) =
      indexed index a.role a.typ (codeNumber a.core.code) (ss.map (OriginalHereditaryExpansion.jobNumber c)) := by
  induction ss generalizing index with
  | nil => rfl
  | cons s ss ih => rw [decorate,List.map_cons,childEncoding,List.map_cons,indexed,ih]

theorem jobsEncoding : OriginalHereditaryRuntimeWorkTargets.JobsEncoding := by
  intro n c a
  rw [jobs,decorateEncoding,indexedRange]
  simp only [OriginalHereditaryAnnotatedExpansion.values,Nat.zero_add,List.length_map]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkEncodingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkEncodingProof
