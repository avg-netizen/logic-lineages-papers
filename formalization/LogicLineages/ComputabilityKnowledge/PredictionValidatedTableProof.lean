module
public import LogicLineages.ComputabilityKnowledge.PredictionValidatedTableTargets
public import LogicLineages.ComputabilityKnowledge.PredictionValidatedBodyProof
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteRenamingProof
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteSerializationProof
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryParameterLayoutProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionValidatedTableProof
open Turing Turing.ToPartrec
open PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality PredictionBinarySentinel
open PredictionFiniteRenaming PredictionFiniteSerialization PredictionValidatedTable PredictionValidatedTableTargets
local instance : DecidableEq TapeAlphabet := PredictionCompilerAlphabetEqualityProof.workDecidableEq

private theorem action_roundtrip {a : Nat} (s : TM0.Stmt (Fin (a + 3))) :
    finiteStmt (PredictionCompilerFiniteTable.action s) = s := by
  cases s with
  | move d => cases d <;> rfl
  | write b => rfl

private theorem assembled (c : Code) :
    PredictionFiniteSerialization.finiteMachine (finiteData c) = PredictionValidatedTable.finiteMachine c := by
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

private theorem serialized_support {q a : Nat} (start : Fin (q + 1)) (m : FinMachine q a) :
    TM0.Supports (PredictionFiniteAlphabet.machine (table start m)) {s | s < q + 1} := by
  constructor
  · change 0 < q + 1
    omega
  · intro s b s' op h hs
    change s < q + 1 at hs
    change (PredictionFiniteAlphabet.lookup (table start m) s b.val).map _ = some (s', op) at h
    rw [PredictionFiniteSerializationProof.exactTransitionLookup q a start m ⟨s, hs⟩ b] at h
    simp only [Option.map_map] at h
    obtain ⟨z, _, hz⟩ := Option.map_eq_some_iff.mp h
    have he : z.1.val = s' := congrArg Prod.fst hz
    change s' < q + 1
    rw [← he]
    exact z.1.isLt

theorem boundedNumericBody : BoundedNumericBody := by
  intro c
  exact ⟨(PredictionFiniteSerializationProof.exactNumericLayout _ _ (entry c) (finiteData c)).2.2,
    (entry c).isLt, serialized_support (entry c) (finiteData c)⟩

private theorem numeric_step (c : Code) (x : TM0.Cfg TapeAlphabet Label)
    (hx : x.q ∈ PredictionValidatedBody.states c) :
    PredictionCompilerFiniteExecution.tableStep (finiteData c) (numericCfg c x) =
      (TM0.step PredictionValidatedBody.machine x).map (numericCfg c) := by
  have hr := PredictionFiniteRenamingProof.exactRenamedStep TapeAlphabet Label
    PredictionValidatedBody.machine (PredictionValidatedBody.states c) binaryAlphabetTail
    alphabet_complete x (List.mem_cons_of_mem _ hx)
  have hr' : (TM0.step PredictionValidatedBody.machine x).map (finiteCfg c) =
      TM0.step (PredictionValidatedTable.finiteMachine c) (finiteCfg c x) := hr
  have hs := serialized (finiteData c) (finiteCfg c x)
  rw [assembled, ← hr'] at hs
  simp only [Option.map_map, Function.comp_def] at hs
  have hn : (fun y : TM0.Cfg TapeAlphabet Label => embedCfg (finiteCfg c y)) = numericCfg c := by
    funext y
    rfl
  exact hs.trans (congrArg (fun f => (TM0.step PredictionValidatedBody.machine x).map f) hn)

private theorem actual_simulation (c : Code) :
    StateTransition.Respects (TM0.step PredictionValidatedBody.machine)
      (PredictionCompilerFiniteExecution.tableStep (finiteData c))
      (fun x d => x.q ∈ PredictionValidatedBody.states c ∧ numericCfg c x = d) := by
  intro x _ hx
  obtain ⟨hx, rfl⟩ := hx
  cases he : TM0.step PredictionValidatedBody.machine x with
  | none => rw [numeric_step c x hx, he]; rfl
  | some y =>
    refine ⟨numericCfg c y, ⟨?_, rfl⟩, Relation.TransGen.single ?_⟩
    · exact TM0.step_supports PredictionValidatedBody.machine
        (PredictionValidatedBodyProof.actualFiniteSupport c) he hx
    · rw [numeric_step c x hx, he]; rfl

theorem fullNumericEvaluation : FullNumericEvaluation := by
  intro c v
  apply Part.ext
  intro d
  have hi : (PredictionValidatedBody.initial c v).q ∈ PredictionValidatedBody.states c ∧
      numericCfg c (PredictionValidatedBody.initial c v) = numericCfg c (PredictionValidatedBody.initial c v) :=
    ⟨PredictionValidatedBodyProof.entrySupported c v, rfl⟩
  constructor
  · intro hd
    obtain ⟨x, hx, hex⟩ := StateTransition.tr_eval_rev (actual_simulation c) hi hd
    exact (Part.mem_map_iff _).2 ⟨x, hex, hx.2⟩
  · intro hd
    obtain ⟨x, hx, rfl⟩ := (Part.mem_map_iff _).1 hd
    obtain ⟨d, hd, hed⟩ := StateTransition.tr_eval (actual_simulation c) hi hx
    rw [hd.2]
    exact hed

private theorem raw_index (b : Bool) : rawIndex b = PredictionFiniteAlphabet.inputSymbol b := by
  cases b
  · exact PredictionBinarySentinelProof.exactBinarySlots.1
  · exact PredictionBinarySentinelProof.exactBinarySlots.2.1

private theorem symbol_index {q a : Nat} (start : Fin (q + 1)) (m : FinMachine q a)
    (s : Fin (a + 3)) : PredictionFiniteAlphabet.symbol (table start m) s.val = s := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt s.isLt

private theorem prepared_congr {q a : Nat} (start : Fin (q + 1)) (m : FinMachine q a)
    (word : List Nat) (xs : List Bool) (ys : List (Fin (a + 3)))
    (h : List.append (α := Fin (a + 3)) (word.map (PredictionFiniteAlphabet.symbol (table start m))) (rawBits a xs) = ys) :
    preparedAt start m word xs = (⟨start.val, Tape.mk₁ ys⟩ : TM0.Cfg (Fin (a + 3)) Nat) :=
  congrArg (fun w => (⟨start.val, Tape.mk₁ w⟩ : TM0.Cfg (Fin (a + 3)) Nat)) h

theorem exactPreparedInput : ExactPreparedInput := by
  intro c e xs
  have hm : (PredictionBinaryParameterLayout.numericWord e).map
      (PredictionFiniteAlphabet.symbol (numericTable c)) =
      (PredictionBinaryParameterLayout.parameterWord e).map (toFinite binaryAlphabetTail) := by
    rw [← PredictionBinaryParameterLayoutProof.exactNumericWord e, List.map_map]
    apply List.map_congr_left
    intro a _
    exact symbol_index (entry c) (finiteData c) (toFinite binaryAlphabetTail a)
  have hb : (xs.map rawSymbol).map (toFinite binaryAlphabetTail) = rawBits workSymbols.length xs := by
    rw [List.map_map]
    apply List.map_congr_left
    intro b _
    apply Fin.ext
    exact raw_index b
  change (⟨(entry c).val, (Tape.mk₁ (PredictionCompilerFiniteExecution.sourceInput [inputNat xs, e])).map
    (toFinite binaryAlphabetTail)⟩ : TM0.Cfg (Fin (workSymbols.length + 3)) Nat) = _
  rw [Tape.map_mk₁, PredictionBinaryParameterLayoutProof.exactParameterLayout, List.map_append]
  exact (prepared_congr (entry c) (finiteData c) _ xs _ (congrArg₂ List.append hm hb.symm)).symm

private theorem terminal_raw (c : Code) (v : List Nat) (d : TM0.Cfg TapeAlphabet Label)
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

theorem universalNumericBody : UniversalNumericBody := by
  obtain ⟨U, hU⟩ := PredictionValidatedBodyProof.universalBinaryBody
  refine ⟨U, ?_⟩
  intro e xs b
  rw [← hU e xs b]
  constructor
  · rintro ⟨d, hd, hb⟩
    rw [fullNumericEvaluation] at hd
    obtain ⟨x, hx, rfl⟩ := (Part.mem_map_iff _).1 hd
    apply (Part.mem_map_iff _).2
    refine ⟨x, hx, ?_⟩
    change (toFinite binaryAlphabetTail x.Tape.head).val = PredictionFiniteAlphabet.inputSymbol b at hb
    rw [terminal_raw U [inputNat xs, e] x hx] at hb
    change rawIndex (PredictionValidatedBody.readout x) = _ at hb
    rw [raw_index] at hb
    cases hr : PredictionValidatedBody.readout x <;> cases b <;>
      simp_all [PredictionFiniteAlphabet.inputSymbol]
  · intro h
    obtain ⟨x, hx, hr⟩ := (Part.mem_map_iff _).1 h
    refine ⟨numericCfg U x, ?_, ?_⟩
    · rw [fullNumericEvaluation]
      exact Part.mem_map _ hx
    · change (toFinite binaryAlphabetTail x.Tape.head).val = _
      rw [terminal_raw U [inputNat xs, e] x hx, hr]
      exact raw_index b

end LogicLineages.ComputabilityKnowledge.PredictionValidatedTableProof
