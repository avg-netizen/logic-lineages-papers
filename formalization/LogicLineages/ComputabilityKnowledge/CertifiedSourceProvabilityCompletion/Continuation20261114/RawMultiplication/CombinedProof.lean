module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplication.Zero.NativeProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplication.Zero.ArithmeticProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplication.Succ.NativeProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplication.Succ.ArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplication.CombinedProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261113.HistoryRuleSuffix SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem nativeRefinement : Targets.NativeRefinement := by
 intro old hold
 exact Succ.NativeProof.nativeRefinement (Zero.arithmeticLeaf old) (Zero.NativeProof.nativeRefinement old hold)

theorem internalZero : Targets.ZeroInternalArithmetic := by
 intro n p old qtag ltag ptag ctag atag vtag hq hl hp hc ha hv ctx raw
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid vtag raw
 let G := [H]
 let ln := Zero.lineCall qtag raw
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 have hi : Computes p G (Zero.arithmeticLeaf old) (ln ::ᵥ nil) (.succ .zero) := by
  intro tag ht
  obtain ⟨h⟩ := Zero.ArithmeticProof.innerArithmetic n p old qtag tag ptag ctag atag vtag hq ht hp hc ha hv ctx raw
  exact ⟨.mp (.base h) hh⟩
 obtain ⟨hout⟩ := RawCumulativeArithmetic.ArithmeticProof.chooseBoth p G Succ.recognizer
  (Zero.arithmeticLeaf old) (constant 1 1) (ln ::ᵥ nil) (.succ .zero)
  hi (constantValue p G (ln ::ᵥ nil) 1) ltag hl
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplication.CombinedProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplication.CombinedProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplication.CombinedProof.nativeRefinement
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplication.CombinedProof.internalZero
