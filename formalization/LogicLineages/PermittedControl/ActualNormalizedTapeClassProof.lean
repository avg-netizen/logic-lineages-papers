module
public import LogicLineages.PermittedControl.ActualNormalizedTapeTargets
import LogicLineages.PermittedControl.ActualNormalizedTapeCertificateProof
import LogicLineages.PermittedControl.ActualRankedZeroClassSelectionProof
import LogicLineages.PermittedControl.ActualRankedZeroClassFiniteProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNormalizedTape
open OrdinalComparison FieldComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum
open ActualZeroClassReplacement ActualWeightedReadNormalization ActualRankedRowColumns
open ActualRankedZeroClass

theorem exactTapeRankedClass : ExactTapeRankedClass := by
  intro f ρ r c raw xs annotations C bounded tape aligned actualC
  let row := rankedRow r c raw
  let selected := classReads f C xs annotations
  let columns := finiteClassColumns r selected
  have unique := tape.unique
  have inRanked := exactTapeRankedMembers f ρ raw xs r c bounded tape
  obtain ⟨sub,_,charge,nonempty,leading⟩ := exactClassSelection f ρ C xs annotations aligned
  have distinct : (selected.map (fun rd => rd.1.2)).Nodup := (sub.map _).nodup unique
  have paidSelected (rd : Read) (chosen : rd ∈ selected) :
      NonlinearOperand rd.1.2 ∧ IsInRankedColumn row rd :=
    ⟨charge rd chosen,inRanked rd (sub.subset chosen)⟩
  obtain ⟨valueKeys,countKeys,coefficient⟩ := finiteClassFacts row selected distinct paidSelected
  have valueSupport : columns.1 ⊆ row.value.support := by
    intro key member
    obtain ⟨rd,source,operand⟩ := (valueKeys key).mp member
    obtain ⟨seen,_,facts⟩ := chargedKey row rd (paidSelected rd source).1 (paidSelected rd source).2
    cases seen with
    | inl v =>
        obtain ⟨literal,active,_⟩ := facts
        have same : v = key := (valueOperand r).injective (literal.symm.trans operand)
        exact same ▸ active
    | inr n =>
        exact False.elim (distinctColumns key n (operand.symm.trans facts.1))
  have countSupport : columns.2 ⊆ row.count.support := by
    intro key member
    obtain ⟨rd,source,operand⟩ := (countKeys key).mp member
    obtain ⟨seen,_,facts⟩ := chargedKey row rd (paidSelected rd source).1 (paidSelected rd source).2
    cases seen with
    | inl v =>
        exact False.elim (distinctColumns v key (facts.1.symm.trans operand))
    | inr n =>
        obtain ⟨literal,active,_⟩ := facts
        have same : n = key := (countOperand r).injective (literal.symm.trans operand)
        exact same ▸ active
  have classPresent : columns.1.Nonempty ∨ columns.2.Nonempty := by
    obtain ⟨rd,member⟩ := List.exists_mem_of_ne_nil selected (nonempty.mpr actualC)
    obtain ⟨key,_,facts⟩ := chargedKey row rd (paidSelected rd member).1 (paidSelected rd member).2
    cases key with
    | inl v => exact .inl ⟨v,(valueKeys v).mpr ⟨rd,member,facts.1⟩⟩
    | inr n => exact .inr ⟨n,(countKeys n).mpr ⟨rd,member,facts.1⟩⟩
  exact ⟨valueSupport,countSupport,classPresent,valueKeys,countKeys,leading.trans coefficient⟩

end LogicLineages.PermittedControl.ActualNormalizedTape
