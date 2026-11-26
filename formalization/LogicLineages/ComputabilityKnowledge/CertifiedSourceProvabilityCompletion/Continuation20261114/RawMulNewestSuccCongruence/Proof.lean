module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccCongruence.ReplacementProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccCongruence.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph

open RawSuccCongruence
theorem internalCoreCongruence : Targets.InternalCoreCongruence := by
 intro n p old a x I ctx t u cert index fuel
 obtain ⟨scanTag,hscan⟩ := TwoSol20261113.ReflexivityRecognizer.TermInternalProof.scanInstalled p I.validatorTag I.hv
 obtain ⟨_,_,_,rightTag,_,_,_,hright⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p scanTag hscan
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid I.validatorTag t
 let W := RawReflexivityDispatcher.valid I.validatorTag u
 let A := Formula.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
  (.add (inputRaw I.consTag I.appendTag t u) (inputRaw I.consTag I.appendTag t u)) cert) (.succ .zero)
 let G := [A,W,V]
 have ht : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 have hu : Hilbert.Local T ctx G W := .hypothesis (by simp [G])
 have hinput : Hilbert.Local T ctx G A := .hypothesis List.mem_cons_self
 obtain ⟨hsucc⟩ := RawSuccCongruence.ValidityProof.internalSuccessorValidity n p I.validatorTag I.pairTag I.consTag I.hv I.hp I.hc ctx t
 have hst := Hilbert.Local.mp (.base hsucc) ht
 obtain ⟨href⟩ := RawMulLeftCongruence.StatementChecks.exactReflexivity n p old a x I.toNewestEquality.toCongruences.toNewest
  ctx (RawSuccReplace.succValue I.consTag t) index fuel
 have hself := Hilbert.Local.mp (.base href) hst
 obtain ⟨hreplace⟩ := ReplacementProof.replacementCore p old a x I t u index fuel
 have hrep := Hilbert.Local.mp (Hilbert.Local.mp (.base hreplace) ht) hu
 obtain ⟨hmp1⟩ := LiteralCoreMP.StatementChecks.coreMP (RawMulLeftReplace.logicalLeaf (RawMulLeftCongruence.previousLogical old)) a x n p
  I.itag I.lengthTag I.appendTag I.pairTag I.consTag rightTag I.dropTag I.lookupTag I.dtag
  I.hi I.hlength I.ha I.hp I.hc hright I.hdrop I.hlookup I.hdispatcher I.mpTag I.qctag I.hmp I.hqc
  ctx .zero (inputRaw I.consTag I.appendTag t u) (intermediateRaw I.consTag I.appendTag t u)
  (RawSuccReplaceCertificate.certificate I.consTag I.replaceTag t u) cert index fuel
 have hinputs1 : Hilbert.Local T ctx G (LiteralCoreMP.inputAcceptance I.qctag I.appendTag I.consTag .zero
  (inputRaw I.consTag I.appendTag t u) (intermediateRaw I.consTag I.appendTag t u)
  (RawSuccReplaceCertificate.certificate I.consTag I.replaceTag t u) cert index fuel) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hrep) hinput
 have hfirst := Hilbert.Local.mp (.base hmp1) hinputs1
 obtain ⟨hmp2⟩ := LiteralCoreMP.StatementChecks.coreMP (RawMulLeftReplace.logicalLeaf (RawMulLeftCongruence.previousLogical old)) a x n p
  I.itag I.lengthTag I.appendTag I.pairTag I.consTag rightTag I.dropTag I.lookupTag I.dtag
  I.hi I.hlength I.ha I.hp I.hc hright I.hdrop I.hlookup I.hdispatcher I.mpTag I.qctag I.hmp I.hqc
  ctx .zero (selfRaw I.consTag I.appendTag t) (outputRaw I.consTag I.appendTag t u)
  (firstCertificate I.mpTag I.replaceTag I.consTag I.appendTag t u cert)
  (RawCumulativeLogical.certificate I.consTag I.reflexivityTag (RawSuccReplace.succValue I.consTag t)) index fuel
 have hinputs2 : Hilbert.Local T ctx G (LiteralCoreMP.inputAcceptance I.qctag I.appendTag I.consTag .zero
  (selfRaw I.consTag I.appendTag t) (outputRaw I.consTag I.appendTag t u)
  (firstCertificate I.mpTag I.replaceTag I.consTag I.appendTag t u cert)
  (RawCumulativeLogical.certificate I.consTag I.reflexivityTag (RawSuccReplace.succValue I.consTag t)) index fuel) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hfirst) hself
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
  (Hilbert.Local.discharge (.mp (.base hmp2) hinputs2))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccCongruence.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccCongruence.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccCongruence.Proof.internalCoreCongruence
