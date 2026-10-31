module
public import LogicLineages.ModelsAlgebra.Forests.CotreeMachineParikhTargets
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerGrammarStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCountsStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeMachineParikh.Proof
open RankedParse ProfileAutomatonEncoding ForestParseRepresentationCotree
open ForestParseRepresentationStates ForestParseRepresentationCounts

theorem stateTransitionExact : Targets.StateTransitionExact := by
  intro M _ o n c q
  have hc : (fun B => (List.ofFn (fun i => stateSet M (c i))).count B) = childCounts M c :=
    funext (fun B => ForestParseRepresentationCounts.Proof.childCountExact M (n + 2) c B)
  have hf := CotreePresburgerGrammar.StatementChecks.formulaGrammarExact M.State (M.node o) q
    (List.ofFn (fun i => stateSet M (c i)))
  rw [hc] at hf
  exact (ForestParseRepresentationStatesGrammar.Proof.stateGrammarExact M o n c q).trans hf.symm

theorem tableTransitionExact : Targets.TableTransitionExact := by
  intro T o n c q
  letI : LinearOrder T.toMachine.State := inferInstanceAs (LinearOrder (Fin T.size))
  exact stateTransitionExact T.toMachine o n c q

theorem encodingRunExact : Targets.EncodingRunExact := by
  intro M n e t
  induction t with
  | atom => rfl
  | node o s t hs ht =>
    change e (M.node o (e.symm (machineRun (numberMachine M e).toMachine s))
      (e.symm (machineRun (numberMachine M e).toMachine t))) = e (M.node o (machineRun M s) (machineRun M t))
    rw [hs, ht]
    simp

theorem stateEncoding (M : Machine) {n : Nat} (e : M.State ≃ Fin n) (C : Cotree) (q : M.State) :
    q ∈ stateSet M C ↔ e q ∈ stateSet (numberMachine M e).toMachine C := by
  constructor
  · intro h
    obtain ⟨t, ht, hr⟩ := (ForestParseRepresentationStates.Proof.stateSetMem M C q).mp h
    exact (ForestParseRepresentationStates.Proof.stateSetMem (numberMachine M e).toMachine C (e q)).mpr
      ⟨t, ht, (encodingRunExact M n e t).trans (congrArg e hr)⟩
  · intro h
    obtain ⟨t, ht, hr⟩ := (ForestParseRepresentationStates.Proof.stateSetMem (numberMachine M e).toMachine C (e q)).mp h
    exact (ForestParseRepresentationStates.Proof.stateSetMem M C q).mpr
      ⟨t, ht, e.injective ((encodingRunExact M n e t).symm.trans hr)⟩

theorem numberedTransitionExact : Targets.NumberedTransitionExact := by
  intro M k e o n c q
  exact (stateEncoding M e (.node o n c) q).trans
    (tableTransitionExact (numberMachine M e) o n c (e q))

end LogicLineages.ModelsAlgebra.Forests.CotreeMachineParikh.Proof
