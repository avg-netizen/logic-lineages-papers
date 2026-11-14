module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalRetention.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCongruence
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
abbrev previousLogical (old : Program 1) : Program 1 :=
 RawMulLeftReplace.logicalLeaf (RawMulLeftCongruence.previousLogical old)
/-- Keep the entire paid arithmetic-template/producer installation and its old
checker intact. New checker fields are distinct, never cast from old CORE. -/
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 toArithmetic : ArithmeticTemplateEvaluation.Installation p old a x where
 universalLineTag : Nat
 universalLogicalTag : Nat
 universalDispatcherTag : Nat
 universalIteratorTag : Nat
 universalCoreTag : Nat
 huniversalLine : (nodes p)[universalLineTag]? = some ⟨2,RawUniversalReplace.lineConstructor⟩
 huniversalLogical : (nodes p)[universalLogicalTag]? = some ⟨1,RawUniversalReplace.logicalLeaf (previousLogical old)⟩
 huniversalDispatcher : (nodes p)[universalDispatcherTag]? = some ⟨4,RawUniversalReplaceDispatcher.dispatcher (previousLogical old) (RawMulNewestAddition.arithmetic a) x⟩
 huniversalIterator : (nodes p)[universalIteratorTag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (RawUniversalReplaceCertificate.kernel (previousLogical old) (RawMulNewestAddition.arithmetic a) x)⟩
 huniversalCore : (nodes p)[universalCoreTag]? = some ⟨5,RawUniversalReplaceCertificate.checker (previousLogical old) (RawMulNewestAddition.arithmetic a) x⟩
def eqRaw {ctx : Nat} (c a : Nat) (t u : Term ctx) : Term ctx := RawUniversalReplace.binaryValue c a 0 t u
def outputRaw {ctx : Nat} (c a : Nat) (t u : Term ctx) : Term ctx :=
 eqRaw c a (RawUniversalReplace.universalValue c t) (RawUniversalReplace.universalValue c u)
def selfRaw {ctx : Nat} (c a : Nat) (t : Term ctx) : Term ctx :=
 RawReflexivity.equalityValue c a (RawUniversalReplace.universalValue c t)
def intermediateRaw {ctx : Nat} (c a : Nat) (t u : Term ctx) : Term ctx :=
 LiteralRawMP.implicationRaw a c (selfRaw c a t) (outputRaw c a t u)
def certificate {ctx : Nat} (mp q ref c a : Nat) (t u input : Term ctx) : Term ctx :=
 LiteralMPRun.certificate mp .zero (outputRaw c a t u)
  (LiteralMPRun.certificate mp .zero (intermediateRaw c a t u)
   (RawUniversalReplaceCertificate.certificate c q t u) input)
  (RawCumulativeLogical.certificate c ref (RawUniversalReplace.universalValue c t))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCongruence
