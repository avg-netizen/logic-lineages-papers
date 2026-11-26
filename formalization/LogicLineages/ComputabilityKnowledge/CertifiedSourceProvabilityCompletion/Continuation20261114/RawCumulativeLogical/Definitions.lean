module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplaceCertificate.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeLogical
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- Both actual logical refinements are chosen before source construction. -/
def logical (old : Program 1) : Program 1 := RawSuccReplace.logicalLeaf (ReflexivitySource.logical old)
abbrev dispatcher (old a : Program 1) (x : Program 3) : Program 4 :=
 HistoryDispatcher.lineDispatcher LiteralSyntaxValidator.lineValidator (logical old) a x
abbrev kernel (old a : Program 1) (x : Program 3) : Program 3 :=
 HistoryKernel.kernel LiteralSyntaxValidator.lineValidator (logical old) a x
abbrev checker (old a : Program 1) (x : Program 3) : Program 5 :=
 LiteralKernelSource.coreChecker LiteralSyntaxValidator.lineValidator (logical old) a x
  LiteralCheckerAuxiliaries.bound LiteralCheckerAuxiliaries.initial LiteralCheckerAuxiliaries.finalizer
abbrev verifier (old a : Program 1) (x : Program 3) : Program 5 := SixSol20261112.Fuel.verifier (checker old a x)
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) where
 qtag : Nat
 ptag : Nat
 ctag : Nat
 atag : Nat
 vtag : Nat
 ftag : Nat
 ltag : Nat
 btag : Nat
 dtag : Nat
 hq : (nodes p)[qtag]? = some ⟨1,RawReflexivity.lineConstructor⟩
 hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩
 hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩
 ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩
 hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩
 hf : (nodes p)[ftag]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩
 hl : (nodes p)[ltag]? = some ⟨1,TwoSol20261113.ReflexivityCertificate.validity⟩
 hb : (nodes p)[btag]? = some ⟨1,logical old⟩
 hd : (nodes p)[dtag]? = some ⟨4,dispatcher old a x⟩
structure CertificateInstallation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 Installation p old a x where
 itag : Nat
 qctag : Nat
 utag : Nat
 hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator
  (kernel old a x)⟩
 hqc : (nodes p)[qctag]? = some ⟨5,checker old a x⟩
 hu : (nodes p)[utag]? = some ⟨5,verifier old a x⟩
def certificate {ctx : Nat} (ctag qtag : Nat) (raw : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (RawReflexivity.lineCall qtag raw) .zero
def output {ctx : Nat} (ptag ctag atag : Nat) (raw : Term ctx) : Term ctx :=
 LiteralCheckerAuxiliaries.successfulState ptag ctag .zero
  (RawReflexivity.equalityValue ctag atag raw) .zero .zero
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeLogical
