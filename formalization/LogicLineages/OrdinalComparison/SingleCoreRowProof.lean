module
public import LogicLineages.OrdinalComparison.SingleCoreRowProgramProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SingleCoreRowCompiler

theorem sign : Targets.ActualSingleCoreFormalRowSign := by
  refine ⟨sign_program,?_⟩
  intro row hv
  dsimp only
  have hparts := parts_program.2.2 row
  have hResult : encodedSingleCoreRowSign (singleCoreRowCode row)=encodedComparisonQueryResult
      ((oneVariableComparisonEncode (.positive (singleCoreRowPart false row)),
        oneVariableComparisonEncode (.positive (singleCoreRowPart true row))),(1,1)) := by
    unfold encodedSingleCoreRowSign
    rw [hparts]
    rfl
  rw [hResult]
  have hSem := semantics row hv
  have hData := (ComparisonAssembly.result_correct
    ((oneVariableComparisonEncode (.positive (singleCoreRowPart false row)),
      oneVariableComparisonEncode (.positive (singleCoreRowPart true row))),(1,1))
    (.positive (singleCoreRowPart false row)) (.positive (singleCoreRowPart true row)) rfl rfl hSem.1 hSem.2.1).1
  refine ⟨hData.1,hData.2.1,?_⟩
  intro t ht
  have hTail := hData.2.2 t ht
  have h0 := hTail.2.2.1
  have h1 := hTail.2.2.2.1
  have h2 := hTail.2.2.2.2
  rw [hSem.2.2 t]
  change (_=0 ↔ (actualFixedLimitProfileEval (singleCoreRowPart false row) t : Int)-
      (actualFixedLimitProfileEval (singleCoreRowPart true row) t : Int)<0) ∧
    (_=1 ↔ (actualFixedLimitProfileEval (singleCoreRowPart false row) t : Int)-
      (actualFixedLimitProfileEval (singleCoreRowPart true row) t : Int)=0) ∧
    (_=2 ↔ 0<(actualFixedLimitProfileEval (singleCoreRowPart false row) t : Int)-
      (actualFixedLimitProfileEval (singleCoreRowPart true row) t : Int))
  change _=0 ↔ actualFixedLimitProfileEval (singleCoreRowPart false row) t<
    actualFixedLimitProfileEval (singleCoreRowPart true row) t at h0
  change _=1 ↔ actualFixedLimitProfileEval (singleCoreRowPart false row) t=
    actualFixedLimitProfileEval (singleCoreRowPart true row) t at h1
  change _=2 ↔ actualFixedLimitProfileEval (singleCoreRowPart true row) t<
    actualFixedLimitProfileEval (singleCoreRowPart false row) t at h2
  omega

theorem full : Targets.FullActualSingleCoreFormalRow := ⟨parts_program,semantics,sign⟩

end LogicLineages.OrdinalComparison.SingleCoreRowCompiler
