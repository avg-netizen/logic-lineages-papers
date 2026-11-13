module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.InstalledProof
open GorbowPRProgram GorbowPRRegistry GorbowPRChildTags
open SixSol20261112.Fuel

theorem pairInstalled {n : Nat} (p : Program n) tag (right : Bool)
    (ht : (nodes p)[tag]? = some ⟨1,decoder right⟩) :
    (nodes p)[pairTag right tag]? = some ⟨2,HistoryCodec.pair⟩ := by
  have houter := Equations.functionChild p tag (outer right) decoderArguments ht
  have hostep := Equations.recursionStepChild p _ (zeroProgram 1) (outerStep right) houter
  have hinner := Equations.functionChild p _ (inner right) outerArguments hostep
  have histep := Equations.recursionStepChild p _ (.projection (2 : Fin 3)) (innerStep right) hinner
  have hforward := Equations.argumentChild p _ HistoryCodec.select (stepArguments right) histep 0
  have hcand := Equations.argumentChild p _ HistoryCodec.difference forwardArguments hforward 0
  have hp := Equations.functionChild p _ HistoryCodec.pair candidateArguments hcand
  exact hp

theorem leftPairInstalled : Targets.LeftPairInstalled := by
  intro n p tag ht
  exact pairInstalled p tag false ht

theorem rightPairInstalled : Targets.RightPairInstalled := by
  intro n p tag ht
  exact pairInstalled p tag true ht

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.InstalledProof
