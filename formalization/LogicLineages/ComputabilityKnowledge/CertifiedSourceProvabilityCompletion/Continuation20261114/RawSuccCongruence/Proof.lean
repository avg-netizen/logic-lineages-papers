module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccCongruence.ValidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccCongruence.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph

/-- Both certificate interfaces share literally the same checker, runtime
and codec nodes; this is AST equality, not extensional calibration. -/
def replacementInstallation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) : RawSuccReplaceCertificate.Installation p (ReflexivitySource.logical old) a x := {
 qtag := I.replaceTag
 ptag := I.ptag
 ctag := I.ctag
 atag := I.atag
 vtag := I.vtag
 ftag := I.ftag
 ltag := I.ltag
 btag := I.btag
 dtag := I.dtag
 itag := I.itag
 qctag := I.qctag
 utag := I.utag
 hq := I.hreplace
 hp := I.hp
 hc := I.hc
 ha := I.ha
 hv := I.hv
 hf := I.hf
 hl := I.hl
 hb := I.hb
 hd := I.hd
 hi := I.hi
 hqc := I.hqc
 hu := I.hu
}

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
 obtain ⟨hsucc⟩ := ValidityProof.internalSuccessorValidity n p I.vtag I.ptag I.ctag I.hv I.hp I.hc ctx t
 have hst := Hilbert.Local.mp (.base hsucc) ht
 obtain ⟨href⟩ := RawCumulativeLogical.StatementChecks.exactCore n p old a x I.toCertificateInstallation
  ctx (RawSuccReplace.succValue I.ctag t) index fuel
 have hself := Hilbert.Local.mp (.base href) hst
 obtain ⟨hreplace⟩ := RawSuccReplaceCertificate.StatementChecks.exactCore n p (ReflexivitySource.logical old) a x
  (replacementInstallation p old a x I) ctx t u index fuel
 have hrep := Hilbert.Local.mp (Hilbert.Local.mp (.base hreplace) ht) hu
 obtain ⟨hmp1⟩ := LiteralCoreMP.StatementChecks.coreMP (RawCumulativeLogical.logical old) a x n p
  I.itag I.lengthTag I.atag I.ptag I.ctag I.rightTag I.dropTag I.lookupTag I.dtag
  I.hi I.hlength I.ha I.hp I.hc I.hright I.hdrop I.hlookup I.hd I.mpTag I.qctag I.hmp I.hqc
  ctx .zero (inputRaw I.ctag I.atag t u) (intermediateRaw I.ctag I.atag t u)
  (RawSuccReplaceCertificate.certificate I.ctag I.replaceTag t u) cert index fuel
 have hinputs1 : Hilbert.Local T ctx G (LiteralCoreMP.inputAcceptance I.qctag I.atag I.ctag .zero
  (inputRaw I.ctag I.atag t u) (intermediateRaw I.ctag I.atag t u)
  (RawSuccReplaceCertificate.certificate I.ctag I.replaceTag t u) cert index fuel) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hrep) hinput
 have hfirst := Hilbert.Local.mp (.base hmp1) hinputs1
 obtain ⟨hmp2⟩ := LiteralCoreMP.StatementChecks.coreMP (RawCumulativeLogical.logical old) a x n p
  I.itag I.lengthTag I.atag I.ptag I.ctag I.rightTag I.dropTag I.lookupTag I.dtag
  I.hi I.hlength I.ha I.hp I.hc I.hright I.hdrop I.hlookup I.hd I.mpTag I.qctag I.hmp I.hqc
  ctx .zero (selfRaw I.ctag I.atag t) (outputRaw I.ctag I.atag t u)
  (firstCertificate I.mpTag I.replaceTag I.ctag I.atag t u cert)
  (RawCumulativeLogical.certificate I.ctag I.qtag (RawSuccReplace.succValue I.ctag t)) index fuel
 have hinputs2 : Hilbert.Local T ctx G (LiteralCoreMP.inputAcceptance I.qctag I.atag I.ctag .zero
  (selfRaw I.ctag I.atag t) (outputRaw I.ctag I.atag t u)
  (firstCertificate I.mpTag I.replaceTag I.ctag I.atag t u cert)
  (RawCumulativeLogical.certificate I.ctag I.qtag (RawSuccReplace.succValue I.ctag t)) index fuel) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hfirst) hself
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
  (Hilbert.Local.discharge (.mp (.base hmp2) hinputs2))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccCongruence.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccCongruence.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccCongruence.Proof.internalCoreCongruence
