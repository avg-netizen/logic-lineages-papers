module
public import LogicLineages.PermittedControl.HighFieldPreparedPacketTargets
import LogicLineages.PermittedControl.InverseComparisonPreparedRowsSupportProof

@[expose] public section
namespace LogicLineages.PermittedControl.HighFieldPreparedPacket
open FieldComparison PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion

theorem packetExact : PacketExact := by
  refine ⟨?_,?_,?_⟩
  · rintro ⟨orientation,tag,answer,H⟩ rankF rankG wanted invalid
    simp [postprocess,not_le_of_gt invalid]
  · intro orientation c rankF rankG wanted admitted
    simp [postprocess,rawConstForm,admitted]
  · intro orientation sign rankF rankG wanted H admitted
    simp [postprocess,rawLinearForm,admitted,preparedPacketCode,preparedTableBytes,
      LowerOperand.code,InverseComparisonPreparedRows.emitCode]

theorem packetShape : PacketShape := by
  have reject : PreparedInput [] .falsity := by
    constructor <;> simp [PlainPreparedFormula,LinearRows.atoms,NormalForm.Formula.variables]
  have accept : PreparedInput [] .truth := by
    constructor <;> simp [PlainPreparedFormula,LinearRows.atoms,NormalForm.Formula.variables]
  refine ⟨reject,?_,?_⟩
  · intro orientation answer wanted
    unfold constantFormula
    split_ifs
    · exact accept
    · exact reject
  · intro orientation sign rankF rankG wanted H
    exact InverseComparisonPreparedRows.preparedShape sign (sortedWanted orientation wanted)
      (.ordinary (lowerRank orientation rankF rankG) H)

end LogicLineages.PermittedControl.HighFieldPreparedPacket
