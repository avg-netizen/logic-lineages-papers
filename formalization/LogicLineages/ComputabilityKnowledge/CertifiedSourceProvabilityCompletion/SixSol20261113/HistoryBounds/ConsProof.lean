module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryBounds.PairProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryBounds.ConsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof
open GorbowPRChildTags List.Vector
open SupportProof PairProof

theorem consFirstStrictBound : Targets.ConsFirstStrictBound := by
  intro n p tag ht ctx a b
  let T := GorbowPRNumeralCalculation.Theory p
  let pairTag := tag+argumentTag Program.succ (fun _ : Fin 1 => HistoryCodec.pair) 0
  have hp := SixSol20261112.Fuel.Equations.argumentChild p tag Program.succ
    (fun _ : Fin 1 => HistoryCodec.pair) ht 0
  obtain ⟨hbound⟩ := pairFirstBound n p pairTag hp ctx a b
  obtain ⟨hs⟩ := weakSuccessor T a (call pairTag (a ::ᵥ b ::ᵥ nil))
  obtain ⟨he⟩ := HistoryCodec.PairProof.internalCons n p tag ht ctx a b
  exact ⟨.mp (.mp (strictTransport a _ _) he) (.mp hs hbound)⟩

theorem consSecondStrictBound : Targets.ConsSecondStrictBound := by
  intro n p tag ht ctx a b
  let T := GorbowPRNumeralCalculation.Theory p
  let pairTag := tag+argumentTag Program.succ (fun _ : Fin 1 => HistoryCodec.pair) 0
  have hp := SixSol20261112.Fuel.Equations.argumentChild p tag Program.succ
    (fun _ : Fin 1 => HistoryCodec.pair) ht 0
  obtain ⟨hbound⟩ := pairSecondBound n p pairTag hp ctx a b
  obtain ⟨hs⟩ := weakSuccessor T b (call pairTag (a ::ᵥ b ::ᵥ nil))
  obtain ⟨he⟩ := HistoryCodec.PairProof.internalCons n p tag ht ctx a b
  exact ⟨.mp (.mp (strictTransport b _ _) he) (.mp hs hbound)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryBounds.ConsProof
