module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCongruence.ValidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCongruence.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph

/-- Both certificate interfaces share literally the same checker, runtime
and codec nodes; this is AST equality, not extensional calibration. -/
def replacementInstallation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) : ReplacementSupport.CoreInstallation p (previousLogical old) (RawMulNewestAddition.arithmetic a) x := {
 qtag := I.universalLineTag, ptag := I.pairTag, ctag := I.consTag, atag := I.appendTag,
 vtag := I.validatorTag, ftag := I.ftag, ltag := I.ltag, btag := I.universalLogicalTag,
 dtag := I.universalDispatcherTag, itag := I.universalIteratorTag, qctag := I.universalCoreTag,
 hq := I.huniversalLine, hp := I.hp, hc := I.hc, ha := I.ha, hv := I.hv, hf := I.hf,
 hl := I.hlineValidator, hb := I.huniversalLogical, hd := I.huniversalDispatcher,
 hi := I.huniversalIterator, hqc := I.huniversalCore }

theorem internalCongruence : Targets.InternalCongruence := by
 intro n p old a x I ctx t u cert index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid I.validatorTag t
 let W := RawReflexivityDispatcher.valid I.validatorTag u
 let A := Formula.equal (LiteralCheckerAcceptance.coreCall I.universalCoreTag index fuel .zero
  (.add (eqRaw I.consTag I.appendTag t u) (eqRaw I.consTag I.appendTag t u)) cert) (.succ .zero)
 let G := [A,W,V]
 have ht : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 have hu : Hilbert.Local T ctx G W := .hypothesis (by simp [G])
 have hinput : Hilbert.Local T ctx G A := .hypothesis List.mem_cons_self
 obtain ⟨hsucc⟩ := ValidityProof.internalUniversalValidity n p I.validatorTag I.pairTag I.consTag I.hv I.hp I.hc ctx t
 have hst := Hilbert.Local.mp (.base hsucc) ht
 obtain ⟨href⟩ := ReflexivityProof.internalReflexivity n p old a x I
  ctx (RawUniversalReplace.universalValue I.consTag t) index fuel
 have hself := Hilbert.Local.mp (.base href) hst
 obtain ⟨hreplace⟩ := ReplacementCoreProof.internalCore n p (previousLogical old) (RawMulNewestAddition.arithmetic a) x
  (replacementInstallation p old a x I) ctx t u index fuel
 have hrep := Hilbert.Local.mp (Hilbert.Local.mp (.base hreplace) ht) hu
 obtain ⟨hmp1⟩ := LiteralCoreMP.StatementChecks.coreMP (RawUniversalReplace.logicalLeaf (previousLogical old)) (RawMulNewestAddition.arithmetic a) x n p
  I.universalIteratorTag I.lengthTag I.appendTag I.pairTag I.consTag I.rightTag I.dropTag I.lookupTag I.universalDispatcherTag
  I.huniversalIterator I.hlength I.ha I.hp I.hc I.hright I.hdrop I.hlookup I.huniversalDispatcher I.mpTag I.universalCoreTag I.hmp I.huniversalCore
  ctx .zero (eqRaw I.consTag I.appendTag t u) (intermediateRaw I.consTag I.appendTag t u)
  (RawUniversalReplaceCertificate.certificate I.consTag I.universalLineTag t u) cert index fuel
 have hinputs1 : Hilbert.Local T ctx G (LiteralCoreMP.inputAcceptance I.universalCoreTag I.appendTag I.consTag .zero
  (eqRaw I.consTag I.appendTag t u) (intermediateRaw I.consTag I.appendTag t u)
  (RawUniversalReplaceCertificate.certificate I.consTag I.universalLineTag t u) cert index fuel) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hrep) hinput
 have hfirst := Hilbert.Local.mp (.base hmp1) hinputs1
 obtain ⟨hmp2⟩ := LiteralCoreMP.StatementChecks.coreMP (RawUniversalReplace.logicalLeaf (previousLogical old)) (RawMulNewestAddition.arithmetic a) x n p
  I.universalIteratorTag I.lengthTag I.appendTag I.pairTag I.consTag I.rightTag I.dropTag I.lookupTag I.universalDispatcherTag
  I.huniversalIterator I.hlength I.ha I.hp I.hc I.hright I.hdrop I.hlookup I.huniversalDispatcher I.mpTag I.universalCoreTag I.hmp I.huniversalCore
  ctx .zero (selfRaw I.consTag I.appendTag t) (outputRaw I.consTag I.appendTag t u)
  (LiteralMPRun.certificate I.mpTag .zero (intermediateRaw I.consTag I.appendTag t u)
   (RawUniversalReplaceCertificate.certificate I.consTag I.universalLineTag t u) cert)
  (RawCumulativeLogical.certificate I.consTag I.reflexivityTag (RawUniversalReplace.universalValue I.consTag t)) index fuel
 have hinputs2 : Hilbert.Local T ctx G (LiteralCoreMP.inputAcceptance I.universalCoreTag I.appendTag I.consTag .zero
  (selfRaw I.consTag I.appendTag t) (outputRaw I.consTag I.appendTag t u)
  (LiteralMPRun.certificate I.mpTag .zero (intermediateRaw I.consTag I.appendTag t u)
   (RawUniversalReplaceCertificate.certificate I.consTag I.universalLineTag t u) cert)
  (RawCumulativeLogical.certificate I.consTag I.reflexivityTag (RawUniversalReplace.universalValue I.consTag t)) index fuel) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hfirst) hself
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
  (Hilbert.Local.discharge (.mp (.base hmp2) hinputs2))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCongruence.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCongruence.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCongruence.Proof.internalCongruence
