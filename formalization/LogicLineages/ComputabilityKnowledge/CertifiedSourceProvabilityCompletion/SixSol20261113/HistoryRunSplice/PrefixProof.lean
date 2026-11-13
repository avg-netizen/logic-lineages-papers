module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem internalPrefixSplice : Targets.InternalPrefixSplice := by
  intro v l a x n p itag ltag atag ptag ctag dtag droptag hi hl ha hp hc hd hdrop ctx left right history out index fuel
  let T := GorbowPRNumeralCalculation.Theory p
  let H := Formula.equal (run itag ptag left (.succ history) left index fuel) (state ptag (.succ out) .zero)
  have h : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
  obtain ⟨hcvt⟩ := ConversionProof.internalBoundConversion v l a x n p itag ltag atag ptag ctag dtag droptag hi hl ha hp hc hd hdrop ctx left (.succ history) index fuel
  obtain ⟨hprop⟩ := PrefixInductionProof.prefixProperty p itag ltag atag ptag ctag v l a x hi hl ha hp hc left right index fuel
  have hr := Derivation.mp (PrefixSupportProof.propertyElim itag ltag atag ptag left right (.succ history) (.succ out) index fuel) hprop
  have hin := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (.base hcvt)) h
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base hr) hin))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixProof
