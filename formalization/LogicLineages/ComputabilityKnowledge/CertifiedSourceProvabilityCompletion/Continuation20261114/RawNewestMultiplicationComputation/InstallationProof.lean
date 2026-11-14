module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationComputation.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationComputation.ValidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationComputation.InstallationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
def zeroInstallation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) : RawMultiplicationCertificates.ZeroCertificate.Installation p
 (RawMulLeftReplace.logicalLeaf (RawMulLeftCongruence.previousLogical old)) (RawCumulativeArithmetic.arithmetic a) x := {
 qtag := I.mulZeroTag, ptag := I.pairTag, ctag := I.consTag, atag := I.appendTag,
 vtag := I.validatorTag, ftag := I.ftag, ltag := I.ltag, btag := I.arithmeticTag,
 dtag := I.dtag, itag := I.itag, qctag := I.qctag, utag := I.utag,
 hq := I.hmulZero, hp := I.hp, hc := I.hc, ha := I.ha,
 hv := I.hv, hf := I.hf, hl := I.hlineValidator, hb := I.harithmetic,
 hd := I.hdispatcher, hi := I.hi, hqc := I.hqc, hu := I.hu }
def succInstallation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) : RawMultiplicationCertificates.SuccCertificate.Installation p
 (RawMulLeftReplace.logicalLeaf (RawMulLeftCongruence.previousLogical old)) (RawCumulativeArithmetic.arithmetic a) x := {
 qtag := I.mulSuccTag, ptag := I.pairTag, ctag := I.consTag, atag := I.appendTag,
 vtag := I.validatorTag, ftag := I.ftag, ltag := I.ltag, btag := I.arithmeticTag,
 dtag := I.dtag, itag := I.itag, qctag := I.qctag, utag := I.utag,
 hq := I.hmulSucc, hp := I.hp, hc := I.hc, ha := I.ha,
 hv := I.hv, hf := I.hf, hl := I.hlineValidator, hb := I.harithmetic,
 hd := I.hdispatcher, hi := I.hi, hqc := I.hqc, hu := I.hu }
def congruenceInstallation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) : RawMulNewestSuccIteration.Installation p old (RawMulNewestAddition.arithmetic a) x := {
 toCongruence := I.toEvaluator.toAddition.toCongruence,
 rightTag := I.rightTag, hright := I.hright,
 leftTag := I.leftTag, stepTag := I.congruenceStepTag, iteratorTag := I.congruenceIteratorTag, prefixTag := I.prefixTag,
 hleft := I.hleft, hstep := I.hcongruenceStep, hiterator := I.hcongruenceIterator, hprefix := I.hprefix }
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationComputation.InstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationComputation.InstallationProof
