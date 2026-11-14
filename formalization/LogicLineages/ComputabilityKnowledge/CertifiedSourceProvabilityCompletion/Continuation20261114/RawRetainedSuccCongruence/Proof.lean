module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccCongruence.ReplacementProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccCongruence.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph

open RawSuccCongruence
theorem internalCoreCongruence : Targets.InternalCoreCongruence := by
 intro n p old a x I ctx t u cert index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid I.vtag t
 let W := RawReflexivityDispatcher.valid I.vtag u
 let A := Formula.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
  (.add (inputRaw I.ctag I.atag t u) (inputRaw I.ctag I.atag t u)) cert) (.succ .zero)
 let G := [A,W,V]
 have ht : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 have hu : Hilbert.Local T ctx G W := .hypothesis (by simp [G])
 have hinput : Hilbert.Local T ctx G A := .hypothesis List.mem_cons_self
 obtain ⟨hsucc⟩ := RawSuccCongruence.ValidityProof.internalSuccessorValidity n p I.vtag I.ptag I.ctag I.hv I.hp I.hc ctx t
 have hst := Hilbert.Local.mp (.base hsucc) ht
 obtain ⟨href⟩ := RawEqualityComposition.StatementChecks.exactReflexivity n p old a x I.toEquality
  ctx (RawSuccReplace.succValue I.ctag t) index fuel
 have hself := Hilbert.Local.mp (.base href) hst
 obtain ⟨hreplace⟩ := ReplacementProof.replacementCore p old a x I t u index fuel
 have hrep := Hilbert.Local.mp (Hilbert.Local.mp (.base hreplace) ht) hu
 obtain ⟨hmp1⟩ := LiteralCoreMP.StatementChecks.coreMP (RawRightReplace.logicalLeaf (RawCumulativeLogical.logical old)) a x n p
  I.itag I.lengthTag I.atag I.ptag I.ctag I.rightTag I.dropTag I.lookupTag I.dtag
  I.hi I.hlength I.ha I.hp I.hc I.hright I.hdrop I.hlookup I.hd I.mpTag I.qctag I.hmp I.hqc
  ctx .zero (inputRaw I.ctag I.atag t u) (intermediateRaw I.ctag I.atag t u)
  (RawSuccReplaceCertificate.certificate I.ctag I.replaceTag t u) cert index fuel
 have hinputs1 : Hilbert.Local T ctx G (LiteralCoreMP.inputAcceptance I.qctag I.atag I.ctag .zero
  (inputRaw I.ctag I.atag t u) (intermediateRaw I.ctag I.atag t u)
  (RawSuccReplaceCertificate.certificate I.ctag I.replaceTag t u) cert index fuel) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hrep) hinput
 have hfirst := Hilbert.Local.mp (.base hmp1) hinputs1
 obtain ⟨hmp2⟩ := LiteralCoreMP.StatementChecks.coreMP (RawRightReplace.logicalLeaf (RawCumulativeLogical.logical old)) a x n p
  I.itag I.lengthTag I.atag I.ptag I.ctag I.rightTag I.dropTag I.lookupTag I.dtag
  I.hi I.hlength I.ha I.hp I.hc I.hright I.hdrop I.hlookup I.hd I.mpTag I.qctag I.hmp I.hqc
  ctx .zero (selfRaw I.ctag I.atag t) (outputRaw I.ctag I.atag t u)
  (firstCertificate I.mpTag I.replaceTag I.ctag I.atag t u cert)
  (RawCumulativeLogical.certificate I.ctag I.reflexivityTag (RawSuccReplace.succValue I.ctag t)) index fuel
 have hinputs2 : Hilbert.Local T ctx G (LiteralCoreMP.inputAcceptance I.qctag I.atag I.ctag .zero
  (selfRaw I.ctag I.atag t) (outputRaw I.ctag I.atag t u)
  (firstCertificate I.mpTag I.replaceTag I.ctag I.atag t u cert)
  (RawCumulativeLogical.certificate I.ctag I.reflexivityTag (RawSuccReplace.succValue I.ctag t)) index fuel) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hfirst) hself
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
  (Hilbert.Local.discharge (.mp (.base hmp2) hinputs2))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccCongruence.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccCongruence.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccCongruence.Proof.internalCoreCongruence
