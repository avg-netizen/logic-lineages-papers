module
public import LogicLineages.OrdinalComparison.SourceBlankHaltingReductionTargets
public import LogicLineages.ComputabilityKnowledge.PredictionUniformBinaryCompilerProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceBlankHaltingReduction.Proof
open Turing LogicLineages.ComputabilityKnowledge
open PredictionFiniteAlphabet PredictionUniformBinaryCompiler
open PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality PredictionBinarySentinel
open PredictionFiniteRenaming PredictionFiniteSerialization
local instance : DecidableEq TapeAlphabet := PredictionCompilerAlphabetEqualityProof.workDecidableEq
attribute [local irreducible] workSymbols PredictionValidatedTable.finiteData PredictionValidatedBody.states
private theorem raw_symbols (p : Table) (xs : List Bool) :
    xs.map (fun b => symbol p (inputSymbol b)) = PredictionValidatedTable.rawBits p.1 xs := by
  apply List.map_congr_left
  intro b _
  apply Fin.ext
  cases b
  · exact (PredictionFiniteAlphabetProof.literalInputSymbols p).2.1
  · exact (PredictionFiniteAlphabetProof.literalInputSymbols p).2.2

private theorem prefix_initial (p : Table) (q : Nat) (word : List Nat) (xs : List Bool) :
    toCfg (PredictionNumericPrefix.assembled p q word)
      (initial (PredictionNumericPrefix.assembled p q word) xs) =
      PredictionNumericPrefixExecution.initial p q word (PredictionValidatedTable.rawBits p.1 xs) := by
  have hi := PredictionFiniteAlphabetProof.exactInitialTape (PredictionNumericPrefix.assembled p q word) xs
  rw [raw_symbols] at hi
  exact hi

private theorem prefix_eval (p : Table) (q : Nat) (word : List Nat) (xs : List Bool)
    (hlen : p.2.2.length ≤ q * width p)
    (hclosed : TM0.Supports (machine p) {s | s < q}) (hstart : p.2.1 < q) :
    StateTransition.eval (TM0.step (PredictionNumericPrefix.machine p q word))
      (toCfg (PredictionNumericPrefix.assembled p q word) (initial (PredictionNumericPrefix.assembled p q word) xs)) =
    StateTransition.eval (TM0.step (machine p))
      (PredictionNumericPrefixExecution.prepared p word (PredictionValidatedTable.rawBits p.1 xs)) :=
  (congrArg (StateTransition.eval (TM0.step (PredictionNumericPrefix.machine p q word))) (prefix_initial p q word xs)).trans
    (PredictionNumericPrefixExecutionProof.exactPrefixEvaluation p q word hlen hclosed _ hstart)

private theorem raw_index (b : Bool) : rawIndex b = PredictionFiniteAlphabet.inputSymbol b := by
  cases b
  · exact PredictionBinarySentinelProof.exactBinarySlots.1
  · exact PredictionBinarySentinelProof.exactBinarySlots.2.1

private theorem terminal_raw (c : Turing.ToPartrec.Code) (v : List Nat) (d : TM0.Cfg TapeAlphabet PredictionValidatedBody.Label)
    (hd : d ∈ StateTransition.eval (TM0.step PredictionValidatedBody.machine) (PredictionValidatedBody.initial c v)) :
    d.Tape.head = rawSymbol (PredictionValidatedBody.readout d) := by
  change d ∈ StateTransition.eval (TM0.step PredictionValidatedBody.machine)
    (PredictionValidatedBody.sourceCfg (PredictionCompilerFiniteExecution.sourceInit c v)) at hd
  rw [PredictionValidatedBodyProof.fullBodyComposition] at hd
  obtain ⟨y, _, hdy⟩ := Part.mem_bind_iff.mp hd
  obtain ⟨z, hz, rfl⟩ := (Part.mem_map_iff _).1 hdy
  rw [PredictionValidatingMachineProof.exactValidatorEvaluation] at hz
  obtain ⟨b, _, rfl⟩ := Option.map_eq_some_iff.mp (Part.mem_ofOption.mp hz)
  cases b <;> rfl


private theorem numeric_terminal (c : Turing.ToPartrec.Code) (v : List Nat)
    (d : TM0.Cfg (Fin (workSymbols.length+3)) Nat)
    (hd : d ∈ PredictionValidatedTable.numericEval c v) :
    ∃ b : Bool, d.Tape.head.val = inputSymbol b := by
  rw [PredictionValidatedTableProof.fullNumericEvaluation] at hd
  obtain ⟨x,hx,rfl⟩ := (Part.mem_map_iff _).1 hd
  refine ⟨PredictionValidatedBody.readout x, ?_⟩
  change (toFinite binaryAlphabetTail x.Tape.head).val = _
  rw [terminal_raw c v x hx]
  exact raw_index _

private theorem prepared_terminal (c : Turing.ToPartrec.Code) (e : Nat) (xs : List Bool)
    (d : TM0.Cfg (Fin (width (PredictionValidatedTable.numericTable c))) Nat)
    (hd : d ∈ StateTransition.eval
      (TM0.step (PredictionFiniteAlphabet.machine (PredictionValidatedTable.numericTable c)))
      (PredictionNumericPrefixExecution.prepared (PredictionValidatedTable.numericTable c)
        (PredictionBinaryParameterLayout.numericWord e)
        (PredictionValidatedTable.rawBits (PredictionValidatedTable.numericTable c).1 xs))) :
    ∃ b : Bool, d.Tape.head.val = inputSymbol b := by
  apply numeric_terminal c [inputNat xs,e] d
  change d ∈ StateTransition.eval
    (PredictionCompilerFiniteExecution.tableStep (PredictionValidatedTable.finiteData c))
    (PredictionValidatedTable.numericCfg c (PredictionValidatedBody.initial c [inputNat xs,e]))
  exact (congrArg (fun cfg => d ∈ StateTransition.eval
    (PredictionCompilerFiniteExecution.tableStep (PredictionValidatedTable.finiteData c)) cfg)
      (PredictionValidatedTableProof.exactPreparedInput c e xs)).mpr hd

private theorem assembled_terminal (c : Turing.ToPartrec.Code) (e : Nat) (xs : List Bool)
    (d : TM0.Cfg (Fin (width (PredictionValidatedTable.numericTable c))) Nat)
    (hd : d ∈ StateTransition.eval
      (TM0.step (PredictionNumericPrefix.machine (PredictionValidatedTable.numericTable c)
        (PredictionValidatedTable.bodyStates c) (PredictionBinaryParameterLayout.numericWord e)))
      (toCfg (PredictionNumericPrefix.assembled (PredictionValidatedTable.numericTable c)
        (PredictionValidatedTable.bodyStates c) (PredictionBinaryParameterLayout.numericWord e))
        (initial (PredictionNumericPrefix.assembled (PredictionValidatedTable.numericTable c)
          (PredictionValidatedTable.bodyStates c) (PredictionBinaryParameterLayout.numericWord e)) xs))) :
    ∃ b : Bool, d.Tape.head.val = inputSymbol b := by
  obtain ⟨hlen,hstart,hclosed⟩ := PredictionValidatedTableProof.boundedNumericBody c
  rw [prefix_eval _ _ _ xs (Nat.le_of_eq hlen) hclosed hstart] at hd
  exact prepared_terminal c e xs d hd

private def terminalProperty (p : Table) (xs : List Bool) : Prop :=
  ∀ d, d ∈ StateTransition.eval (TM0.step (PredictionFiniteAlphabet.machine p))
    (toCfg p (initial p xs)) → ∃ b : Bool, d.Tape.head.val = inputSymbol b

private theorem compile_decodes (c : Turing.ToPartrec.Code) (e : Nat) :
    decodeTable (compile c e) = PredictionNumericPrefix.assembled
      (PredictionValidatedTable.numericTable c) (PredictionValidatedTable.bodyStates c)
      (PredictionBinaryParameterLayout.numericWord e) :=
  PredictionFiniteAlphabetProof.effectiveDecoding.2 _

private theorem compiled_terminal (c : Turing.ToPartrec.Code) (e : Nat) (xs : List Bool) :
    ∀ d, d ∈ machineEval (compile c e) xs → ∃ b : Bool, d.Tape.head.val = inputSymbol b := by
  change terminalProperty (decodeTable (compile c e)) xs
  rw [compile_decodes]
  exact assembled_terminal c e xs

theorem validatedTerminalBridge : Targets.ValidatedTerminalBridge := by
  intro c e xs
  refine ⟨compiled_terminal c e xs, ?_⟩
  constructor
  · intro h
    obtain ⟨d,hd⟩ := Part.dom_iff_mem.mp h
    obtain ⟨b,hb⟩ := compiled_terminal c e xs d hd
    apply Part.dom_iff_mem.mpr
    refine ⟨b, Part.mem_bind_iff.mpr ⟨d,hd,?_⟩⟩
    apply Part.mem_ofOption.mpr
    exact (PredictionUniformBinaryCompilerProof.physicalBinaryReadout _ b).2 hb
  · intro h
    obtain ⟨b,hb⟩ := Part.dom_iff_mem.mp h
    obtain ⟨d,hd,_⟩ := Part.mem_bind_iff.mp hb
    exact Part.dom_iff_mem.mpr ⟨d,hd⟩
end LogicLineages.OrdinalComparison.SourceBlankHaltingReduction.Proof
