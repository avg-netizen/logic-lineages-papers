module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnaryEvaluation.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnaryEvaluation.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem internalZero : Targets.InternalZero := by
 intro n p old a x I ctx index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let z : Term ctx := RawAdditionComputation.zeroRaw I.consTag
 let nz : Term ctx := LiteralNumeralPrefix.numeralCall I.numeralTag .zero
 let cert := RawCumulativeLogical.certificate I.consTag I.reflexivityTag z
 obtain ⟨hz⟩ := LiteralNumeralPrefix.EquationsProof.zero (ctx := ctx) p I.numeralTag I.consTag I.hnumeral I.hc
 obtain ⟨hnv⟩ := RawMulNewestAdditionIteration.InvariantSupport.numeralValid p old a x I.toCurrent.toComputation.toEvaluator (.zero : Term ctx)
 have hc := HistoryLookup.DestructorProof.unaryCallCongruence (T := T) I.validatorTag nz z hz
 have hv : Derivation T (RawReflexivityDispatcher.valid I.validatorTag z) :=
  Logic.trans _ _ _ (Support.equalitySymmetry _ _ hc) hnv
 obtain ⟨hr⟩ := RawMulLeftCongruence.ReflexivityProof.internalReflexivity n p old (RawMulNewestAddition.arithmetic a) x
  I.toCurrent.toComputation.toEvaluator.toAddition.toCongruence.toNewestEquality.toCongruences.toNewest ctx z index fuel
 have hself := GorbowTheoryProof.Derivation.mp hr hv
 have hm := RawNewestMultiplicationIteration.InvariantProof.moveRight (T := T)
  I.qctag I.consTag I.appendTag index fuel z z cert nz
 exact ⟨GorbowTheoryProof.Derivation.mp (GorbowTheoryProof.Derivation.mp hm (Support.equalitySymmetry _ _ hz)) hself⟩

theorem internalSuccessor : Targets.InternalSuccessor := by
 intro n p old a x I ctx t m cert index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let nm := LiteralNumeralPrefix.numeralCall I.numeralTag m
 let V := RawReflexivityDispatcher.valid I.validatorTag t
 let A := RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel t nm cert
 let G := [A,V]
 have ht : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 have hin : Hilbert.Local T ctx G A := .hypothesis List.mem_cons_self
 obtain ⟨hnv⟩ := RawMulNewestAdditionIteration.InvariantSupport.numeralValid p old a x I.toCurrent.toComputation.toEvaluator m
 obtain ⟨hcon⟩ := RawMulNewestSuccCongruence.StatementChecks.exactCoreCongruence n p old (RawMulNewestAddition.arithmetic a) x
  I.toCurrent.toComputation.toEvaluator.toAddition.toCongruence ctx t nm cert index fuel
 have hout := Hilbert.Local.mp (.mp (.mp (.base hcon) ht) (.base hnv)) hin
 obtain ⟨hs⟩ := LiteralNumeralPrefix.EquationsProof.successor p I.numeralTag I.consTag I.hnumeral I.hc m
 have hm := RawNewestMultiplicationIteration.InvariantProof.moveRight (T := T)
  I.qctag I.consTag I.appendTag index fuel (RawAdditionComputation.succRaw I.consTag t)
  (RawAdditionComputation.succRaw I.consTag nm)
  (RawSuccCongruence.certificate I.mpTag I.replaceTag I.reflexivityTag I.consTag I.appendTag t nm cert)
  (LiteralNumeralPrefix.numeralCall I.numeralTag (.succ m))
 have hfinal := Hilbert.Local.mp (.mp (.base hm) (.base (Support.equalitySymmetry _ _ hs))) hout
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hfinal))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnaryEvaluation.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnaryEvaluation.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnaryEvaluation.Proof.internalZero
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnaryEvaluation.Proof.internalSuccessor
