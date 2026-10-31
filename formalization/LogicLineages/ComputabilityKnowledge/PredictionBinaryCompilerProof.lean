module
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryCompilerTargets
public import LogicLineages.ComputabilityKnowledge.PredictionBinarySentinelProof
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryOutputLayoutProof
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerTapeSupportProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionBinaryCompilerProof
open Turing Turing.ToPartrec Turing.PartrecToTM2
open PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality PredictionBinarySentinel
open PredictionBinaryCompiler PredictionBinaryCompilerTargets

private def advance {α : Type} (f : α → Option α) : Nat → α → Option α
  | 0, x => some x
  | n + 1, x => (f x).bind (advance f n)

private theorem advance_reaches {α : Type} (f : α → Option α) (n : Nat) (x y : α)
    (h : advance f n x = some y) : StateTransition.Reaches f x y := by
  induction n generalizing x with
  | zero => cases Option.some.inj h; exact Relation.ReflTransGen.refl
  | succ n ih =>
    obtain ⟨z, hz, hzy⟩ := Option.bind_eq_some_iff.mp h
    have hxz : StateTransition.Reaches f x z := Relation.ReflTransGen.single hz
    exact hxz.trans (ih z hzy)

private theorem prefix_reaches (c : Code) (xs : List Bool) :
    StateTransition.Reaches (TM0.step (machine c)) (initial xs)
      (embed (PredictionCompilerFiniteExecution.sourceInit c [inputNat xs])) := by
  apply advance_reaches _ 4
  change advance (TM0.step (machine c)) 4
    (⟨.prefix 0, Tape.mk₁ (xs.map rawSymbol)⟩ : TM0.Cfg TapeAlphabet Label) = _
  simp [advance, machine, TM0.step, TM0.init, embed, PredictionBinaryPrefixMachine.bodyStart,
    PredictionCompilerFiniteExecution.sourceInit, PredictionBinarySentinelProof.exactInputLayout xs,
    Tape.mk₁, Tape.mk₂, Tape.move_left_mk', Tape.write_mk', ListBlank.cons_mk]

private theorem body_step (c : Code) (x y : TM0.Cfg TapeAlphabet PostLabel)
    (h : TM0.step postMachine x = some y) :
    TM0.step (machine c) (embed x) = some (embed y) := by
  cases x with
  | mk q t =>
    obtain ⟨⟨q', op⟩, hp, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [TM0.step, machine, embed, hp]

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

private theorem source_output (c : Code) (v : List Nat) (b : Bool)
    (hw : [b.toNat] ∈ Code.eval c v) :
    TM1to0.trCfg tapeMachine (PredictionBinaryOutputLayout.outputConfig b) ∈
      StateTransition.eval (TM0.step postMachine) (PredictionCompilerFiniteExecution.sourceInit c v) := by
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  have hs : PartrecToTM2.halt [b.toNat] ∈
      StateTransition.eval (TM2.step tr) (PartrecToTM2.init c v) := by
    rw [PartrecToTM2.tr_eval]
    exact Part.mem_map _ hw
  obtain ⟨x, hx, hex⟩ := StateTransition.tr_eval (TM2to1.tr_respects tr) (initial_stack c v) hs
  have hxe := (PredictionBinaryOutputLayoutProof.exactHaltLayout b x).1 hx
  subst x
  obtain ⟨y, hy, hey⟩ := StateTransition.tr_eval (TM1to0.tr_respects tapeMachine) rfl hex
  rw [hy]
  exact hey

private theorem output_reaches (c : Code) (b : Bool) :
    StateTransition.Reaches (TM0.step (machine c))
      (embed (TM1to0.trCfg tapeMachine (PredictionBinaryOutputLayout.outputConfig b))) (final b) := by
  apply advance_reaches _ 2
  cases b <;> rfl

theorem exactBinaryEvaluation : ExactBinaryEvaluation := by
  intro c xs b hb
  have hs := (StateTransition.mem_eval).1 (source_output c [inputNat xs] b hb)
  have hr : StateTransition.Reaches (TM0.step (machine c))
      (embed (PredictionCompilerFiniteExecution.sourceInit c [inputNat xs]))
      (embed (TM1to0.trCfg tapeMachine (PredictionBinaryOutputLayout.outputConfig b))) :=
    hs.1.lift embed (body_step c)
  apply StateTransition.mem_eval.2
  exact ⟨(prefix_reaches c xs).trans (hr.trans (output_reaches c b)), rfl⟩

theorem exactRawOutput : ExactRawOutput := by
  intro c b
  exact ⟨rfl, rfl⟩

theorem actualFiniteSupport : ActualFiniteSupport := by
  intro c
  have hp (i : Fin 4) : Label.prefix i ∈ states c := by
    simp only [states, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inr (Or.inl (List.mem_ofFn.mpr ⟨i, rfl⟩)))
  have hb : PredictionBinaryPrefixMachine.bodyStart c ∈ postLabels c Cont'.halt :=
    (PredictionCompilerTapeSupportProof.actualPostCompilerClosure c Cont'.halt).1
  constructor
  · exact hp 0
  · intro q a q' op h hq
    cases q with
    | «prefix» i =>
      simp only [machine] at h
      split at h <;> try { cases h; exact hp _ }
      split at h <;> try { cases h; exact hp _ }
      split at h <;> try { cases h; exact hp _ }
      cases h
      simp [states, hb]
    | body l =>
      have hl : l ∈ postLabels c Cont'.halt := by simpa [states] using hq
      cases he : postMachine l a with
      | none =>
        simp only [machine, he, Option.mem_def, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp [states]
      | some z =>
        rcases z with ⟨l', op'⟩
        simp only [machine, he, Option.mem_def, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have hs := (PredictionCompilerTapeSupportProof.actualPostCompilerClosure c Cont'.halt).2 he hl
        change l' ∈ postLabels c Cont'.halt at hs
        simpa [states] using hs
    | write =>
      simp only [machine, Option.mem_def, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp [states]
    | stop => cases h

end LogicLineages.ComputabilityKnowledge.PredictionBinaryCompilerProof
