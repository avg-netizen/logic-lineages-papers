module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeLogical.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeLogical.LogicalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherPrimitivesProof
theorem internalReflexivity : Targets.InternalReflexivity := by
 intro n p old qtag ltag ptag ctag atag vtag hq hl hp hc ha hv ctx raw
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid vtag raw
 let G := [H]
 let line := RawReflexivity.lineCall qtag raw
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 have hinner : Computes p G (ReflexivitySource.logical old) (line ::ᵥ nil) (.succ .zero) := by
  intro tag ht
  obtain ⟨h⟩ := RawReflexivity.StatementChecks.exactInternalLogical n p old qtag tag ptag ctag atag vtag
   hq ht hp hc ha hv ctx raw
  exact ⟨.mp (.base h) hh⟩
 have hone := constantValue p G (line ::ᵥ nil) 1
 obtain ⟨hout⟩ := RawCumulativeArithmetic.ArithmeticProof.chooseBoth p G RawSuccReplace.recognizer (ReflexivitySource.logical old)
  (constant 1 1) (line ::ᵥ nil) (.succ .zero) hinner hone ltag hl
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeLogical.LogicalProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeLogical.LogicalProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeLogical.LogicalProof.internalReflexivity
