module
public import LogicLineages.ComputabilityKnowledge.PredictionValidatedBodyTargets
public import LogicLineages.ComputabilityKnowledge.PredictionValidatingMachineProof
public import LogicLineages.ComputabilityKnowledge.PredictionAttachExitProof
public import LogicLineages.ComputabilityKnowledge.PredictionFixedUniversalProof
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerTapeSupportProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionValidatedBodyProof
open Turing Turing.ToPartrec Turing.PartrecToTM2
open PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality PredictionBinarySentinel
open PredictionValidatedBody PredictionValidatedBodyTargets

private def exit (x : TM0.Cfg TapeAlphabet PostLabel) := PredictionValidatingMachine.initial x.Tape

private theorem flatten_step (z : TM0.Cfg TapeAlphabet PostLabel ⊕
    TM0.Cfg TapeAlphabet PredictionValidatingMachine.Label) :
    (PredictionAttachExit.step (TM0.step postMachine) (TM0.step PredictionValidatingMachine.machine) exit z).map flatten =
      TM0.step machine (flatten z) := by
  cases z with
  | inl x =>
    cases x with
    | mk q t =>
      cases hp : postMachine q t.head with
      | none => simp [PredictionAttachExit.step, TM0.step, machine, flatten, sourceCfg, validatorCfg,
          exit, PredictionValidatingMachine.initial, hp, Tape.write_self]
      | some z =>
        rcases z with ⟨q', op⟩
        cases op <;> simp [PredictionAttachExit.step, TM0.step, machine, flatten, sourceCfg, hp]
  | inr x =>
    cases x with
    | mk q t =>
      simp only [PredictionAttachExit.step, TM0.step, machine, flatten, validatorCfg, Option.map_map]
      congr 1

private theorem respects_from_step {α β : Type} (f : α → Option α) (g : β → Option β)
    (h : α → β) (hs : ∀ x, (f x).map h = g (h x)) :
    StateTransition.Respects f g (fun x d => h x = d) := by
  apply StateTransition.fun_respects.2
  intro x
  cases he : f x with
  | none => exact (hs x).symm.trans (by rw [he]; rfl)
  | some y => exact Relation.TransGen.single ((hs x).symm.trans (by rw [he]; rfl))

theorem fullBodyComposition : FullBodyComposition := by
  intro x
  have h := StateTransition.tr_eval'
    (PredictionAttachExit.step (TM0.step postMachine) (TM0.step PredictionValidatingMachine.machine) exit)
    (TM0.step machine) flatten
    (respects_from_step _ _ flatten flatten_step) (Sum.inl x)
  rw [PredictionAttachExit.fullComposition] at h
  simpa only [Part.map_eq_map, Part.map_map, Function.comp_def, Part.map_bind, flatten, exit] using h

private theorem initial_stack (c : Code) (v : List Nat) :
    letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
    TM2to1.TrCfg (PartrecToTM2.init c v)
      (TM1.init (PredictionCompilerFiniteExecution.sourceInput v) : TM1.Cfg TapeAlphabet TapeLabel Store) := by
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  have h := TM2to1.trCfg_init (Γ := StackAlphabet) (Λ := Λ') (σ := Store) K'.main (trList v)
  convert h using 1 <;> try rfl
  apply congrArg (fun s => (⟨some (trNormal c Cont'.halt), none, s⟩ : PartrecToTM2.Cfg'))
  funext j
  cases j <;> simp [K'.elim, Function.update]

private theorem source_forward (c : Code) (v w : List Nat) (hw : w ∈ Code.eval c v) :
    ∃ x : TM1.Cfg TapeAlphabet TapeLabel Store, TM2to1.TrCfg (PartrecToTM2.halt w) x ∧
      TM1to0.trCfg tapeMachine x ∈ StateTransition.eval (TM0.step postMachine)
        (PredictionCompilerFiniteExecution.sourceInit c v) := by
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  have hs : PartrecToTM2.halt w ∈ StateTransition.eval (TM2.step tr) (PartrecToTM2.init c v) := by
    rw [PartrecToTM2.tr_eval]
    exact Part.mem_map _ hw
  obtain ⟨x, hx, hex⟩ := StateTransition.tr_eval (TM2to1.tr_respects tr) (initial_stack c v) hs
  obtain ⟨y, hy, hey⟩ := StateTransition.tr_eval (TM1to0.tr_respects tapeMachine) rfl hex
  refine ⟨x, hx, ?_⟩
  rw [hy]
  exact hey

private theorem source_reverse (c : Code) (v : List Nat) (y : TM0.Cfg TapeAlphabet PostLabel)
    (hy : y ∈ StateTransition.eval (TM0.step postMachine) (PredictionCompilerFiniteExecution.sourceInit c v)) :
    ∃ w, w ∈ Code.eval c v ∧ ∃ x : TM1.Cfg TapeAlphabet TapeLabel Store,
      TM2to1.TrCfg (PartrecToTM2.halt w) x ∧ TM1to0.trCfg tapeMachine x = y := by
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  obtain ⟨x, hx, hex⟩ := StateTransition.tr_eval_rev (TM1to0.tr_respects tapeMachine)
    (show TM1to0.trCfg tapeMachine
      (TM1.init (PredictionCompilerFiniteExecution.sourceInput v) : TM1.Cfg TapeAlphabet TapeLabel Store) =
      PredictionCompilerFiniteExecution.sourceInit c v from rfl) hy
  obtain ⟨z, hz, hez⟩ := StateTransition.tr_eval_rev (TM2to1.tr_respects tr) (initial_stack c v) hex
  rw [PartrecToTM2.tr_eval] at hez
  obtain ⟨w, hw, rfl⟩ := (Part.mem_map_iff _).1 hez
  exact ⟨w, hw, x, hz, hx⟩

theorem actualFiniteSupport : ActualFiniteSupport := by
  intro c
  have hv (v : PredictionValidatingMachine.Label) : Label.validate v ∈ states c := by
    cases v <;> simp [states, validatorLabels]
  constructor
  · exact hv .check
  · intro q a q' op h hq
    cases q with
    | source l =>
      have hl : l ∈ postLabels c Cont'.halt := by simpa [states] using hq
      cases he : postMachine l a with
      | none =>
        simp only [machine, he, Option.mem_def, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact hv .check
      | some z =>
        rcases z with ⟨l', op'⟩
        simp only [machine, he, Option.mem_def, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have hs := (PredictionCompilerTapeSupportProof.actualPostCompilerClosure c Cont'.halt).2 he hl
        change l' ∈ postLabels c Cont'.halt at hs
        simpa [states] using hs
    | validate v =>
      change (PredictionValidatingMachine.machine v a).map (fun z => (Label.validate z.1, z.2)) = some (q', op) at h
      obtain ⟨⟨v', op'⟩, _, hpair⟩ := Option.map_eq_some_iff.mp h
      cases hpair
      exact hv v'

theorem entrySupported : EntrySupported := by
  intro c v
  have h : (PredictionCompilerFiniteExecution.sourceInit c v).q ∈ postLabels c Cont'.halt :=
    (PredictionCompilerTapeSupportProof.actualPostCompilerClosure c Cont'.halt).1
  simpa [initial, sourceCfg, states] using h

theorem universalBinaryBody : UniversalBinaryBody := by
  obtain ⟨U, hU⟩ := PredictionFixedUniversal.fixedUniversal
  refine ⟨U, ?_⟩
  intro e xs b
  constructor
  · intro h
    obtain ⟨d, hd, hread⟩ := (Part.mem_map_iff _).1 h
    change d ∈ StateTransition.eval (TM0.step machine)
      (sourceCfg (PredictionCompilerFiniteExecution.sourceInit U [inputNat xs, e])) at hd
    rw [fullBodyComposition] at hd
    obtain ⟨y, hy, hdy⟩ := Part.mem_bind_iff.mp hd
    obtain ⟨z, hz, rfl⟩ := (Part.mem_map_iff _).1 hdy
    change PredictionValidatingMachine.readout z = b at hread
    obtain ⟨w, hw, t, ht, hty⟩ := source_reverse U [inputNat xs, e] y hy
    rw [hU e xs] at hw
    obtain ⟨n, hn, rfl⟩ := (Part.mem_map_iff _).1 hw
    rw [← hty] at hz
    have hvalid : b ∈ (StateTransition.eval (TM0.step PredictionValidatingMachine.machine)
        (PredictionValidatingMachine.initial t.Tape)).map PredictionValidatingMachine.readout :=
      (Part.mem_map_iff _).2 ⟨z, hz, hread⟩
    have he := (PredictionValidatingMachineProof.sourceBinarySemantics n t b ht).1 hvalid
    rwa [he] at hn
  · intro h
    have hc : [b.toNat] ∈ Code.eval U [inputNat xs, e] := by
      rw [hU e xs]
      exact Part.mem_map _ h
    obtain ⟨t, ht, hy⟩ := source_forward U [inputNat xs, e] [b.toNat] hc
    have hvalid := (PredictionValidatingMachineProof.sourceBinarySemantics b.toNat t b ht).2 rfl
    obtain ⟨z, hz, hread⟩ := (Part.mem_map_iff _).1 hvalid
    apply (Part.mem_map_iff _).2
    refine ⟨validatorCfg z, ?_, hread⟩
    change validatorCfg z ∈ StateTransition.eval (TM0.step machine)
      (sourceCfg (PredictionCompilerFiniteExecution.sourceInit U [inputNat xs, e]))
    rw [fullBodyComposition]
    exact Part.mem_bind_iff.mpr ⟨TM1to0.trCfg tapeMachine t, hy, (Part.mem_map_iff _).2 ⟨z, hz, rfl⟩⟩

end LogicLineages.ComputabilityKnowledge.PredictionValidatedBodyProof
