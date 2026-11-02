module
public import LogicLineages.OrdinalComparison.OriginalGroundCompilerCodeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalGroundCompilerCode.Proof

theorem exactRecordPackaging : Targets.ExactRecordPackaging := by
  intro k Γ rs hr
  simp [packRecords,NumericAccountData.recordCode,SourceAnnotationCode.operatorSource,
    SourceAnnotationCode.operatorVector,OriginalGroundDataConstruction.operators,
    NumericUnaryChain.operatorCode,Encodable.encodek,List.map_map]
end LogicLineages.OrdinalComparison.Source.OriginalGroundCompilerCode.Proof
