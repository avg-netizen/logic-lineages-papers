module
public import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingCodeTargets
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingTapeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalOperandGroupingCode
open ActualCanonicalOperandGrouping

private theorem decodes (gate : Bool) (ts : List RawTerm) :
    groupCode (gate,Encodable.encode ts) = (groupCheckedRaw gate ts).map Encodable.encode := by
  simp only [groupCode,Encodable.encodek]

theorem exactGroupingCodeCalibration : ExactGroupingCodeCalibration := by
  refine ⟨decodes,?_,?_⟩
  · intro bytes malformed gate
    simp only [groupCode,malformed]
  · intro gate terms
    rw [decodes]
    cases gate
    · rfl
    · change some (Encodable.encode (groupRaw (terms.map encodeTerm))) =
        some (Encodable.encode ((groupTyped terms).map encodeTerm))
      rw [exactCanonicalTape.1 terms]

end LogicLineages.PermittedControl.ActualCanonicalOperandGroupingCode
