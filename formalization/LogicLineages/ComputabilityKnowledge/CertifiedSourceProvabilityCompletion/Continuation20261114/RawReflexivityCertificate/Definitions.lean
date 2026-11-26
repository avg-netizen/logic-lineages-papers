module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivityDispatcher.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivityCertificate
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- Same finite raw interface, with actual iterator, CORE and saturated verifier. -/
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 RawReflexivityDispatcher.Installation p old a x where
 itag : Nat
 qctag : Nat
 utag : Nat
 hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator
  (TwoSol20261113.ReflexivityCertificate.kernel old a x)⟩
 hqc : (nodes p)[qctag]? = some ⟨5,TwoSol20261113.ReflexivityCertificate.checker old a x⟩
 hu : (nodes p)[utag]? = some ⟨5,ReflexivityFuel.checker old a x⟩
def certificate {ctx : Nat} (ctag qtag : Nat) (raw : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (RawReflexivity.lineCall qtag raw) .zero
def output {ctx : Nat} (ptag ctag atag : Nat) (raw : Term ctx) : Term ctx :=
 LiteralCheckerAuxiliaries.successfulState ptag ctag .zero
  (RawReflexivity.equalityValue ctag atag raw) .zero .zero
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivityCertificate
