module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccCongruence.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddition
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- Actual single arithmetic AST containing original addition and multiplication clauses. -/
abbrev arithmetic (a : Program 1) : Program 1 :=
 RawMultiplication.arithmeticLeaf (RawCumulativeArithmetic.arithmetic a)
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 toCongruence : RawMulNewestSuccCongruence.Installation p old (arithmetic a) x where
 zeroTag : Nat
 addTag : Nat
 oldArithmeticTag : Nat
 arithmeticTag : Nat
 hzero : (nodes p)[zeroTag]? = some ⟨1,RawAddZero.lineConstructor⟩
 hadd : (nodes p)[addTag]? = some ⟨2,RawAddSucc.lineConstructor⟩
 holdArithmetic : (nodes p)[oldArithmeticTag]? = some ⟨1,RawCumulativeArithmetic.arithmetic a⟩
 harithmetic : (nodes p)[arithmeticTag]? = some ⟨1,arithmetic a⟩
abbrev zeroRaw := @RawAdditionComputation.zeroRaw
abbrev addRaw := @RawAdditionComputation.addRaw
abbrev succRaw := @RawAdditionComputation.succRaw
abbrev stepCertificate := @RawAdditionComputation.stepCertificate
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddition
