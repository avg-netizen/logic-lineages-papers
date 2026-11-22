module
public import LogicLineages.PermittedControl.OriginalPrintedRawGraphAllocatorTargets
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsCalibrationProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawGraphAllocator
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedCircuitNumericRead (encodeGate)
open OriginalPrintedCircuitNormalization (names baseGate baseGates protectedCeiling firstHidden)

private theorem gateLiteral (g : Gate) :
    outputCode (encodeGate g) = g.output ∧ referencesCode (encodeGate g) = g.references := by
  cases g with
  | base b => cases b <;> exact ⟨rfl,rfl⟩
  | field f =>
    cases f with
    | iterate _ _ _ => exact ⟨rfl,rfl⟩
    | entry int _ _ => cases int <;> exact ⟨rfl,rfl⟩
    | count int _ _ => cases int <;> exact ⟨rfl,rfl⟩

private theorem outputLiteral (g : Gate) : outputCode (encodeGate g) = g.output :=
  (gateLiteral g).1

private theorem referencesLiteral (g : Gate) : referencesCode (encodeGate g) = g.references :=
  (gateLiteral g).2

private theorem namesLiteral (gs : List Gate) :
    namesCode (gs.map encodeGate) = names gs := by
  simp only [namesCode,names,List.map_map,List.flatMap_map,Function.comp_def,
    outputLiteral,referencesLiteral]

private theorem basesLiteral (gs : List Gate) :
    baseCodes (gs.map encodeGate) = (baseGates gs).map (fun g => encodeGate (.base g)) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g with
    | base b =>
      cases b <;> simp [baseCodes,baseGates,baseGate,encodeGate,ih]
    | field f =>
      cases f with
      | iterate _ _ _ => simp [baseCodes,baseGates,baseGate,encodeGate,ih]
      | entry int _ _ => cases int <;> simp [baseCodes,baseGates,baseGate,encodeGate,ih]
      | count int _ _ => cases int <;> simp [baseCodes,baseGates,baseGate,encodeGate,ih]

theorem exactOriginalRawGraphNames : ExactOriginalRawGraphNames :=
  ⟨gateLiteral,namesLiteral,basesLiteral⟩

private theorem liftNames (gs : List OriginalMixedGateSequential.Gate) :
    names (gs.map Gate.base) = OriginalMixedGateNormalization.listedNames gs := by
  simp only [names,OriginalMixedGateNormalization.listedNames,List.map_map,List.flatMap_map,
    Function.comp_def,Gate.output,Gate.references]

private theorem exteriorLiteral (known : List Nat) (p : NormalForm.Formula) :
    exteriorCode (known,p.encode) = OriginalPrintedCircuitNormalizedTerminal.exterior known (.rows p) := by
  simp only [exteriorCode,OriginalPrintedCircuitNormalizedTerminal.exterior,OriginalMixedTerminalTest.testCeiling,
    OriginalMixedTerminalTest.Test.names,MaximalPlainBranchProgramsProof.variables_calibration]

private theorem protectedLiteral (ext : Nat) (gs : List Gate) :
    protectedCode (ext,gs.map encodeGate) = protectedCeiling ext gs := by
  simp only [protectedCode,protectedCeiling,namesLiteral]

private theorem firstLiteral (ext : Nat) (gs : List Gate) :
    firstHiddenCode (ext,gs.map encodeGate) = firstHidden ext gs := by
  rw [firstHiddenCode,basesLiteral,protectedLiteral]
  change (namesCode ((baseGates gs).map (fun g => encodeGate (.base g)))).foldr max
      (protectedCeiling ext gs) + 1 =
    (OriginalMixedGateNormalization.listedNames (baseGates gs)).foldr max
      (protectedCeiling ext gs) + 1
  have eq : (baseGates gs).map (fun g => encodeGate (.base g)) =
      ((baseGates gs).map Gate.base).map encodeGate := by
    simp only [List.map_map,Function.comp_def]
  rw [eq,namesLiteral,liftNames]

theorem exactOriginalRawGraphAllocator : ExactOriginalRawGraphAllocator := by
  refine ⟨exteriorLiteral,protectedLiteral,firstLiteral,?_⟩
  intro known p gates
  rw [initialCode,exteriorLiteral,firstLiteral]

end LogicLineages.PermittedControl.OriginalPrintedRawGraphAllocator
