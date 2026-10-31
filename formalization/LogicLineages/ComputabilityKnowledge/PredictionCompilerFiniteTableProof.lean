module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerFiniteTableTargets
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteRenamingProof
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteSerializationProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerFiniteTableProof
open Turing Turing.ToPartrec Turing.PartrecToTM2
open PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality PredictionCompilerFiniteTable
open PredictionCompilerFiniteTableTargets PredictionFiniteRenaming PredictionFiniteSerialization
local instance : DecidableEq TapeAlphabet := PredictionCompilerAlphabetEqualityProof.workDecidableEq
local instance : DecidableEq PostLabel := PredictionCompilerPostEqualityProof.postDecidableEq

private theorem action_roundtrip {a : Nat} (s : TM0.Stmt (Fin (a + 3))) :
    finiteStmt (action s) = s := by
  cases s with
  | move d => cases d <;> rfl
  | write b => rfl

theorem exactActionAssembly : ExactActionAssembly := by
  intro c k
  funext q b
  simp only [finiteMachine, finiteData, Option.map_map, Function.comp_def, action_roundtrip]
  simp

theorem exactTableCode : ExactTableCode := by
  intro c k
  simp [numericCode, numericTable, code, PredictionFiniteAlphabet.decodeTable,
    Encodable.encodek]

private theorem alphabet_complete (a : TapeAlphabet) : a ∈ items alphabetTail := by
  simp only [items, alphabetTail, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (PredictionCompilerAlphabetEqualityProof.completeWorkAlphabet a)))

theorem exactFiniteStep : ExactFiniteStep := by
  intro c k x hx
  letI : Inhabited Λ' := ⟨trNormal c k⟩
  exact PredictionFiniteRenamingProof.exactRenamedStep TapeAlphabet PostLabel postMachine
    (postLabels c k) alphabetTail alphabet_complete x (List.mem_cons_of_mem _ hx)

theorem exactNumericStep : ExactNumericStep := by
  intro c k x hx
  unfold NumericStepAt
  rw [PredictionFiniteSerializationProof.exactSerializedStep,
    exactActionAssembly, ← exactFiniteStep c k x hx]

end LogicLineages.ComputabilityKnowledge.PredictionCompilerFiniteTableProof
