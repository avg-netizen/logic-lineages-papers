module
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryTableTargets
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryCompilerProof
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteRenamingProof
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteSerializationProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionBinaryTableProof
open Turing Turing.ToPartrec
open PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality PredictionBinarySentinel
open PredictionFiniteRenaming PredictionFiniteSerialization PredictionBinaryTable PredictionBinaryTableTargets
local instance : DecidableEq TapeAlphabet := PredictionCompilerAlphabetEqualityProof.workDecidableEq

private theorem action_roundtrip {a : Nat} (s : TM0.Stmt (Fin (a + 3))) :
    finiteStmt (PredictionCompilerFiniteTable.action s) = s := by
  cases s with
  | move d => cases d <;> rfl
  | write b => rfl

private theorem assembled (c : Code) :
    PredictionFiniteSerialization.finiteMachine (finiteData c) = PredictionBinaryTable.finiteMachine c := by
  funext q b
  simp only [PredictionFiniteSerialization.finiteMachine, finiteData,
    Option.map_map, Function.comp_def, action_roundtrip]
  simp

private theorem serialized {q a : Nat} (m : FinMachine q a)
    (x : TM0.Cfg (Fin (a + 3)) (Fin (q + 1))) :
    PredictionCompilerFiniteExecution.tableStep m (embedCfg x) =
      (TM0.step (PredictionFiniteSerialization.finiteMachine m) x).map embedCfg :=
  PredictionFiniteSerializationProof.exactSerializedStep q a 0 m x

private theorem alphabet_complete (a : TapeAlphabet) : a ∈ items binaryAlphabetTail := by
  simp only [items, binaryAlphabetTail, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (PredictionCompilerAlphabetEqualityProof.completeWorkAlphabet a)))

theorem exactCodeDecoding : ExactCodeDecoding := by
  intro c
  simp [numericCode, numericTable, code, PredictionFiniteAlphabet.decodeTable, Encodable.encodek]

theorem exactSourceStep : ExactSourceStep := by
  intro c x hx
  have hr := PredictionFiniteRenamingProof.exactRenamedStep TapeAlphabet Label
    (PredictionBinaryCompiler.machine c) (PredictionBinaryCompiler.states c) binaryAlphabetTail
    alphabet_complete x (List.mem_cons_of_mem _ hx)
  have hr' : (TM0.step (PredictionBinaryCompiler.machine c) x).map (finiteCfg c) =
      TM0.step (PredictionBinaryTable.finiteMachine c) (finiteCfg c x) := hr
  have hs := serialized (finiteData c) (finiteCfg c x)
  rw [assembled, ← hr'] at hs
  simp only [Option.map_map, Function.comp_def] at hs
  have hn : (fun y : TM0.Cfg TapeAlphabet Label => embedCfg (finiteCfg c y)) = numericCfg c := by
    funext y
    rfl
  exact hs.trans (congrArg (fun f => (TM0.step (PredictionBinaryCompiler.machine c) x).map f) hn)

private theorem raw_index (b : Bool) : rawIndex b = PredictionFiniteAlphabet.inputSymbol b := by
  cases b
  · exact PredictionBinarySentinelProof.exactBinarySlots.1
  · exact PredictionBinarySentinelProof.exactBinarySlots.2.1

theorem exactRawInitial : ExactRawInitial := by
  intro c xs
  have hi : finiteCfg c (PredictionBinaryCompiler.initial xs) =
      TM0.init ((xs.map rawSymbol).map (toFinite binaryAlphabetTail)) :=
    TM0.map_init (toFinite binaryAlphabetTail) (toFinite (PredictionBinaryCompiler.states c)) _
  unfold numericCfg
  rw [hi]
  change (⟨0, Tape.mk₁ ((xs.map rawSymbol).map (toFinite binaryAlphabetTail))⟩ :
    TM0.Cfg (Fin (workSymbols.length + 3)) Nat) = rawInitial workSymbols.length xs
  unfold rawInitial
  congr 2
  rw [List.map_map]
  apply List.map_congr_left
  intro b _
  apply Fin.ext
  exact raw_index b

private theorem respects_of_map {α β : Type} (f : α → Option α) (g : β → Option β)
    (h : α → β) (S : α → Prop)
    (closed : ∀ x y, f x = some y → S x → S y)
    (step : ∀ x, S x → g (h x) = (f x).map h) :
    StateTransition.Respects f g (fun x d => S x ∧ h x = d) := by
  intro x _ hx
  obtain ⟨hx, rfl⟩ := hx
  cases he : f x with
  | none => rw [step x hx, he]; rfl
  | some y =>
    refine ⟨h y, ⟨closed x y he hx, rfl⟩, Relation.TransGen.single ?_⟩
    rw [step x hx, he]
    rfl

private theorem actual_simulation (c : Code) :
    StateTransition.Respects (TM0.step (PredictionBinaryCompiler.machine c))
      (PredictionCompilerFiniteExecution.tableStep (finiteData c))
      (fun x d => x.q ∈ PredictionBinaryCompiler.states c ∧ numericCfg c x = d) := by
  apply respects_of_map _ _ _ _
  · intro x y he hx
    exact TM0.step_supports (PredictionBinaryCompiler.machine c)
      (PredictionBinaryCompilerProof.actualFiniteSupport c) he hx
  · exact exactSourceStep c

theorem exactRawEvaluation : ExactRawEvaluation := by
  intro c xs b hb
  obtain ⟨d, hd, hed⟩ := StateTransition.tr_eval (actual_simulation c)
    (show (PredictionBinaryCompiler.initial xs).q ∈ PredictionBinaryCompiler.states c ∧
      numericCfg c (PredictionBinaryCompiler.initial xs) = numericCfg c (PredictionBinaryCompiler.initial xs)
      from ⟨(PredictionBinaryCompilerProof.actualFiniteSupport c).1, rfl⟩)
    (PredictionBinaryCompilerProof.exactBinaryEvaluation c xs b hb)
  refine ⟨d, ?_, ?_⟩
  · unfold numericEval
    rw [← exactRawInitial c xs]
    exact hed
  · rw [← hd.2]
    change (toFinite binaryAlphabetTail (PredictionBinaryCompiler.final b).Tape.head).val = _
    rw [(PredictionBinaryCompilerProof.exactRawOutput c b).1]
    exact raw_index b

end LogicLineages.ComputabilityKnowledge.PredictionBinaryTableProof
