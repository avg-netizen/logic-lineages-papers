module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationComputation.ValidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationComputation.InstallationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
def zeroInstallation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) : RawMultiplicationCertificates.ZeroCertificate.Installation p
 (RawRightReplace.logicalLeaf (RawCumulativeLogical.logical old)) (RawCumulativeArithmetic.arithmetic a) x := {
 qtag := I.mulZeroTag, ptag := I.ptag, ctag := I.ctag, atag := I.atag,
 vtag := I.vtag, ftag := I.ftag, ltag := I.ltag, btag := I.arithmeticTag,
 dtag := I.dtag, itag := I.itag, qctag := I.qctag, utag := I.utag,
 hq := I.hmulZero, hp := I.hp, hc := I.hc, ha := I.ha,
 hv := I.hv, hf := I.hf, hl := I.hl, hb := I.harithmetic,
 hd := I.hd, hi := I.hi, hqc := I.hqc, hu := I.hu }
def succInstallation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) : RawMultiplicationCertificates.SuccCertificate.Installation p
 (RawRightReplace.logicalLeaf (RawCumulativeLogical.logical old)) (RawCumulativeArithmetic.arithmetic a) x := {
 qtag := I.mulSuccTag, ptag := I.ptag, ctag := I.ctag, atag := I.atag,
 vtag := I.vtag, ftag := I.ftag, ltag := I.ltag, btag := I.arithmeticTag,
 dtag := I.dtag, itag := I.itag, qctag := I.qctag, utag := I.utag,
 hq := I.hmulSucc, hp := I.hp, hc := I.hc, ha := I.ha,
 hv := I.hv, hf := I.hf, hl := I.hl, hb := I.harithmetic,
 hd := I.hd, hi := I.hi, hqc := I.hqc, hu := I.hu }
def congruenceInstallation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) : RawRetainedSuccIteration.Installation p old (RawRetainedAddition.arithmetic a) x := {
 toCongruence := I.toEvaluator.toAddition.toCongruence,
 leftTag := I.leftTag, stepTag := I.congruenceStepTag, iteratorTag := I.congruenceIteratorTag, prefixTag := I.prefixTag,
 hleft := I.hleft, hstep := I.hcongruenceStep, hiterator := I.hcongruenceIterator, hprefix := I.hprefix }
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationComputation.InstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationComputation.InstallationProof
