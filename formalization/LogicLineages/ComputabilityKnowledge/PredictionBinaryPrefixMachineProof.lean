module
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryPrefixMachineTargets
public import LogicLineages.ComputabilityKnowledge.PredictionBinarySentinelProof
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerFiniteExecutionProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionBinaryPrefixMachineProof
open Turing Turing.ToPartrec Turing.PartrecToTM2
open PredictionCompilerTapeSupport PredictionBinarySentinel PredictionBinaryPrefixMachine
open PredictionBinaryPrefixMachineTargets

theorem exactFourTransitions : ExactFourTransitions := by
  intro c xs
  change advance c 4 (⟨.prefix 0, Tape.mk₁ (xs.map rawSymbol)⟩ : TM0.Cfg TapeAlphabet Label) = _
  simp [advance, initial, machine, TM0.step, TM0.init, embed, bodyStart,
    PredictionCompilerFiniteExecution.sourceInit, PredictionBinarySentinelProof.exactInputLayout xs,
    Tape.mk₁, Tape.mk₂, Tape.move_left_mk', Tape.write_mk', ListBlank.cons_mk]

theorem exactBodyStep : ExactBodyStep := by
  intro c x
  cases x with | mk q t =>
    simp only [TM0.step, embed, machine, Option.map_map]
    congr 1

private theorem advance_reaches (c : Code) (n : Nat) (x y : TM0.Cfg TapeAlphabet Label)
    (h : advance c n x = some y) : StateTransition.Reaches (TM0.step (machine c)) x y := by
  induction n generalizing x with
  | zero => cases Option.some.inj h; exact Relation.ReflTransGen.refl
  | succ n ih =>
    obtain ⟨z, hz, hzy⟩ := Option.bind_eq_some_iff.mp h
    have hxz : StateTransition.Reaches (TM0.step (machine c)) x z :=
      Relation.ReflTransGen.single hz
    exact hxz.trans (ih z hzy)

private theorem respects_from_step {α β : Type} (f : α → Option α) (g : β → Option β)
    (h : α → β) (hs : ∀ x, g (h x) = (f x).map h) :
    StateTransition.Respects f g (fun x d => h x = d) := by
  apply StateTransition.fun_respects.2
  intro x
  cases he : f x with
  | none => exact (hs x).trans (by rw [he]; rfl)
  | some y => exact Relation.TransGen.single ((hs x).trans (by rw [he]; rfl))

theorem prefixTermination : PrefixTermination := by
  intro c xs
  rw [StateTransition.reaches_eval
    (advance_reaches c 4 (initial xs) _ (exactFourTransitions c xs))]
  have hb := StateTransition.tr_eval_dom
    (respects_from_step (TM0.step postMachine) (TM0.step (machine c)) embed (exactBodyStep c))
    (show embed (PredictionCompilerFiniteExecution.sourceInit c [inputNat xs]) =
      embed (PredictionCompilerFiniteExecution.sourceInit c [inputNat xs]) from rfl)
  have hn := StateTransition.tr_eval_dom
    (PredictionCompilerFiniteExecutionProof.exactReachableSimulation c Cont'.halt)
    (show (PredictionCompilerFiniteExecution.sourceInit c [inputNat xs]).q ∈ postLabels c Cont'.halt ∧
      PredictionCompilerFiniteTable.numericCfg c Cont'.halt
        (PredictionCompilerFiniteExecution.sourceInit c [inputNat xs]) =
      PredictionCompilerFiniteTable.numericCfg c Cont'.halt
        (PredictionCompilerFiniteExecution.sourceInit c [inputNat xs]) from
      ⟨(PredictionCompilerTapeSupportProof.actualPostCompilerClosure c Cont'.halt).1, rfl⟩)
  exact hb.trans (hn.symm.trans (PredictionCompilerFiniteExecutionProof.exactTermination c [inputNat xs]))

end LogicLineages.ComputabilityKnowledge.PredictionBinaryPrefixMachineProof
