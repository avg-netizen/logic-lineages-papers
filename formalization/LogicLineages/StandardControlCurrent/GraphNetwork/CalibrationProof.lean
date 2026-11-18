module
public import LogicLineages.StandardControlCurrent.GraphNetwork.Targets
public import LogicLineages.StandardControlCurrent.PolynomialBoolean.CalibrationProof
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionCodeCalibrationProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.GraphNetwork.CalibrationProof
open OrdinalComparison PolynomialGraphCompletion ExpressionCodeCalibrationProof

 theorem block_rows (b : Block) : Code.blockRows (encodeBlock b) = b.rows := by
  have hc := rowMachineCalibration b.term b.start [] []
  simp only [Code.blockRows,encodeBlock,instructions_calibration,
    hc,List.nil_append,List.headD_cons,Block.rows]

 theorem block_heads (b : Block) : Code.blockHeads (encodeBlock b) = b.term.heads := by
  simp only [Code.blockHeads,encodeBlock,instructions_calibration,instructions_headNames]

 theorem full : Targets.LiteralNetwork := by
  refine ⟨block_rows,?_⟩
  intro d hs bs rs p
  have hr : (bs.map encodeBlock).flatMap Code.blockRows = bs.flatMap Block.rows := by
    simp only [List.flatMap_map,Function.comp_def,block_rows]
  have hh : (bs.map encodeBlock).flatMap Code.blockHeads = bs.flatMap (fun b => b.term.heads) := by
    simp only [List.flatMap_map,Function.comp_def,block_heads]
  simp only [Code.package,Code.decode,sourceCode,Encodable.encodek,Option.getD_some,
    hr,hh,PolynomialBoolean.CalibrationProof.positive_code,PolynomialBoolean.CalibrationProof.graph_code]
  rfl
end LogicLineages.StandardControlCurrent.GraphNetwork.CalibrationProof
