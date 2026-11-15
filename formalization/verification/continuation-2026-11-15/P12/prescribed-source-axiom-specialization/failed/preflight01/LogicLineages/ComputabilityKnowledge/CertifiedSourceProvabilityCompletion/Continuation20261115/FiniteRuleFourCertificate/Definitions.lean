module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourDispatcher.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCertificate.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB SixSol20261113
abbrev kernel (logical arithmetic : Program 1) (x : Program 3) : Program 3 :=
 HistoryKernel.kernel LiteralSyntaxValidator.lineValidator logical arithmetic (SaturatedAxiomLeaf.saturated x)
abbrev checker (logical arithmetic : Program 1) (x : Program 3) : Program 5 :=
 LiteralKernelSource.coreChecker LiteralSyntaxValidator.lineValidator logical arithmetic (SaturatedAxiomLeaf.saturated x)
  LiteralCheckerAuxiliaries.bound LiteralCheckerAuxiliaries.initial LiteralCheckerAuxiliaries.finalizer
abbrev verifier (logical arithmetic : Program 1) (x : Program 3) : Program 5 :=
 SixSol20261112.Fuel.verifier (checker logical arithmetic x)
abbrev root (pF pR logical arithmetic : Program 1) (x : Program 3) : Program 4 :=
 FiniteRuleFourLeaf.sourceRoot pF pR (verifier logical arithmetic x)
/-- Existing literal nodes only. Dispatcher and saturated leaf children must be
recovered from this actual iterator, not supplied as success premises. -/
structure Installation {n : Nat} (p : Program n) (logical arithmetic : Program 1) (x : Program 3) where
 ptag : Nat
 ctag : Nat
 itag : Nat
 qctag : Nat
 utag : Nat
 hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩
 hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩
 hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (kernel logical arithmetic x)⟩
 hqc : (nodes p)[qctag]? = some ⟨5,checker logical arithmetic x⟩
 hu : (nodes p)[utag]? = some ⟨5,verifier logical arithmetic x⟩
/-- Original Line-list encoding, not a surrogate length or evaluator witness. -/
def certificateCode (sigma : Sentence) : Nat :=
 Encodable.encode ([GorbowTheoryChecker.axiomLine 0 sigma] : List GorbowProofChecker.Line)
def rawCode (sigma : Sentence) : Nat := Encodable.encode (GorbowFormulaPrefixCode.encode sigma)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate
