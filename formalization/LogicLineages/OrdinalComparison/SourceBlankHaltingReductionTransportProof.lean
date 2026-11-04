module
public import LogicLineages.OrdinalComparison.SourceBlankHaltingReductionNormalizationProof
public import LogicLineages.OrdinalComparison.SourceBlankHaltingReductionTerminalProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceBlankHaltingReduction.Proof
open Turing LogicLineages.ComputabilityKnowledge
open PredictionFiniteAlphabet PredictionUniformBinaryCompiler
private theorem raw_symbols (p : Table) (xs : List Bool) :
    xs.map (fun b => symbol p (inputSymbol b)) = PredictionValidatedTable.rawBits p.1 xs := by
  apply List.map_congr_left
  intro b _
  apply Fin.ext
  cases b
  · exact (PredictionFiniteAlphabetProof.literalInputSymbols p).2.1
  · exact (PredictionFiniteAlphabetProof.literalInputSymbols p).2.2

private theorem bind_congr {α β : Type} (p q : Part α) (f : α → Part β) (h : p = q) :
    p.bind f = q.bind f := congrArg (fun v => v.bind f) h

private theorem decoded_eval (p : Table) (xs : List Bool) :
    binaryEval (Encodable.encode p) xs =
      (StateTransition.eval (TM0.step (machine p)) (toCfg p (initial p xs))).bind
        (fun d => Part.ofOption (readBit d.Tape.head.val)) := by
  exact congrArg (fun t : Table =>
    (StateTransition.eval (TM0.step (machine t)) (toCfg t (initial t xs))).bind
      (fun d => Part.ofOption (readBit d.Tape.head.val)))
    (PredictionFiniteAlphabetProof.effectiveDecoding.2 p)

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

private theorem binary_prefix_eval (p : Table) (q : Nat) (word : List Nat) (xs : List Bool)
    (hlen : p.2.2.length ≤ q * width p)
    (hclosed : TM0.Supports (machine p) {s | s < q}) (hstart : p.2.1 < q) :
    binaryEval (PredictionNumericPrefix.code p q word) xs =
      (StateTransition.eval (TM0.step (machine p))
        (PredictionNumericPrefixExecution.prepared p word (PredictionValidatedTable.rawBits p.1 xs))).bind
          (fun d => Part.ofOption (readBit d.Tape.head.val)) := by
  exact (decoded_eval (PredictionNumericPrefix.assembled p q word) xs).trans
    (bind_congr _ _ (fun d : TM0.Cfg (Fin (width p)) Nat => Part.ofOption (readBit d.Tape.head.val))
      (prefix_eval p q word xs hlen hclosed hstart))

private theorem binary_mem {α : Type} (p : Part α) (read : α → Nat) (b : Bool) :
    b ∈ p.bind (fun d => Part.ofOption (readBit (read d))) ↔
      ∃ d, d ∈ p ∧ read d = inputSymbol b := by
  simp only [Part.mem_bind_iff, Part.mem_ofOption, Option.mem_def]
  apply exists_congr
  intro d
  exact and_congr_right (fun _ => PredictionUniformBinaryCompilerProof.physicalBinaryReadout (read d) b)

private theorem eval_prepared {q a : Nat} (start : Fin (q + 1))
    (m : PredictionFiniteSerialization.FinMachine q a) (word : List Nat) (xs : List Bool)
    (x : TM0.Cfg (Fin (a + 3)) Nat) (h : x = PredictionValidatedTable.preparedAt start m word xs) :
    StateTransition.eval (PredictionCompilerFiniteExecution.tableStep m) x =
      StateTransition.eval (TM0.step (machine (PredictionFiniteSerialization.table start m)))
        (PredictionNumericPrefixExecution.prepared (PredictionFiniteSerialization.table start m) word
          (PredictionValidatedTable.rawBits a xs)) :=
  congrArg (StateTransition.eval (PredictionCompilerFiniteExecution.tableStep m)) h

private theorem compiled_at {q a : Nat} (start : Fin (q + 1))
    (m : PredictionFiniteSerialization.FinMachine q a) (bound : Nat) (word : List Nat) (xs : List Bool)
    (x : TM0.Cfg (Fin (a + 3)) Nat) (hx : x = PredictionValidatedTable.preparedAt start m word xs)
    (hlen : (PredictionFiniteSerialization.table start m).2.2.length ≤ bound * width (PredictionFiniteSerialization.table start m))
    (hclosed : TM0.Supports (machine (PredictionFiniteSerialization.table start m)) {s | s < bound})
    (hstart : start.val < bound) (b : Bool) :
    b ∈ binaryEval (PredictionNumericPrefix.code (PredictionFiniteSerialization.table start m) bound word) xs ↔
      ∃ d, d ∈ StateTransition.eval (PredictionCompilerFiniteExecution.tableStep m) x ∧
        d.Tape.head.val = inputSymbol b := by
  have he := binary_prefix_eval (PredictionFiniteSerialization.table start m) bound word xs hlen hclosed hstart
  rw [he]
  refine (binary_mem _ (fun d : TM0.Cfg (Fin (a + 3)) Nat => d.Tape.head.val) b).trans ?_
  have hv := eval_prepared start m word xs x hx
  exact (congrArg (fun v => ∃ d, d ∈ v ∧ d.Tape.head.val = inputSymbol b) hv).symm.to_iff

private theorem compiled_semantics (c : Turing.ToPartrec.Code) (e : Nat) (xs : List Bool) (b : Bool) :
    b ∈ binaryEval (compile c e) xs ↔
      ∃ d, d ∈ PredictionValidatedTable.numericEval c [PredictionBinarySentinel.inputNat xs, e] ∧
        d.Tape.head.val = inputSymbol b := by
  obtain ⟨hlen, hstart, hclosed⟩ := PredictionValidatedTableProof.boundedNumericBody c
  exact compiled_at (PredictionValidatedTable.entry c) (PredictionValidatedTable.finiteData c)
    (PredictionValidatedTable.bodyStates c) (PredictionBinaryParameterLayout.numericWord e) xs _
    (PredictionValidatedTableProof.exactPreparedInput c e xs) (Nat.le_of_eq hlen) hclosed hstart b


private theorem normalized_roundtrip (c : Nat.Partrec.Code) :
    Nat.Partrec.Code.ofNatCode (normalizedIndex (Encodable.encode c)) = normalize c := by
  change Denumerable.ofNat Nat.Partrec.Code
    (Encodable.encode (normalize (Denumerable.ofNat Nat.Partrec.Code (Encodable.encode c)))) = _
  rw [Denumerable.ofNat_encode, Denumerable.ofNat_encode]

theorem effectiveBlankReduction : Targets.EffectiveBlankReduction := by
  obtain ⟨U,hU⟩ := PredictionValidatedTableProof.universalNumericBody
  refine ⟨U,(PredictionUniformBinaryCompilerProof.effectiveFixedBodyCompiler U).comp
    normalized_index_primitive, ?_⟩
  intro c
  change (machineEval (compile U (normalizedIndex (Encodable.encode c))) []).Dom ↔ _
  rw [(validatedTerminalBridge U (normalizedIndex (Encodable.encode c)) []).2]
  rw [Part.dom_iff_mem]
  have he (b : Bool) : b ∈ binaryEval (compile U (normalizedIndex (Encodable.encode c))) [] ↔
      b.toNat ∈ (fun _ : Nat => 0) <$> c.eval 0 := by
    rw [compiled_semantics, hU, normalized_roundtrip, normalize_eval]
  constructor
  · rintro ⟨b,hb⟩
    obtain ⟨v,hv,_⟩ := (Part.mem_map_iff _).mp ((he b).mp hb)
    exact Part.dom_iff_mem.mpr ⟨v,hv⟩
  · intro hc
    obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp hc
    exact ⟨false,(he false).mpr ((Part.mem_map_iff _).mpr ⟨v,hv,rfl⟩)⟩
end LogicLineages.OrdinalComparison.SourceBlankHaltingReduction.Proof
