module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.LengthDataProof

public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.DrainProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open SixSol20261112.Fuel NamedArithmeticGraph

theorem internalLengthDrain : Targets.InternalLengthDrain := by
  intro v l a x n p itag ltag atag ptag ctag dtag droptag hi hl ha hp hc hd hdrop ctx code option index fuel
  obtain ⟨hdata⟩ := LengthDataProof.lengthData n p ltag atag droptag ctag hl ha hdrop hc ctx code (.zero : Term ctx) .zero
  have hexhaust := Derivation.mp (.logical (.andLeft _ _)) hdata
  obtain ⟨hremain⟩ := HistoryIteratorDrain.IterationProof.internalIteratorRemaining v l a x n p itag dtag droptag ptag ctag
    hi hd hdrop hp hc ctx (HistoryLengthOffset.lengthCall ltag code) option code index fuel
  exact ⟨Logic.trans _ _ _ hremain hexhaust⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.DrainProof

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.DrainProof
