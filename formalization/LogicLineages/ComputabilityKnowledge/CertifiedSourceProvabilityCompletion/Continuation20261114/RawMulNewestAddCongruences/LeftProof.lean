module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddCongruences.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddCongruences.LeftProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open RawAddLeftCongruence
open SixSol20261112.Fuel NamedArithmeticGraph


theorem internalCongruence : Targets.InternalLeft := by
 intro n p old a x I ctx t u v cert index fuel
 obtain ⟨scanTag,hscan⟩ := TwoSol20261113.ReflexivityRecognizer.TermInternalProof.scanInstalled p I.validatorTag I.hv
 obtain ⟨_,_,_,rightTag,_,_,_,hright⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p scanTag hscan
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid I.validatorTag t
 let W := RawReflexivityDispatcher.valid I.validatorTag u
 let A := Formula.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
  (.add (eqRaw I.consTag I.appendTag t u) (eqRaw I.consTag I.appendTag t u)) cert) (.succ .zero)
 let Z := RawReflexivityDispatcher.valid I.validatorTag v
 let G := [A,Z,W,V]
 have ht : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 have hu : Hilbert.Local T ctx G W := .hypothesis (by simp [G])
 have hv : Hilbert.Local T ctx G Z := .hypothesis (by simp [G])
 have hinput : Hilbert.Local T ctx G A := .hypothesis List.mem_cons_self
 obtain ⟨hadd⟩ := RawAdditionComputation.ValidityProof.internalAdditionValidity n p I.validatorTag I.pairTag I.consTag I.appendTag I.hv I.hp I.hc I.ha ctx v t
 have htv := Hilbert.Local.mp (.mp (.base hadd) hv) ht
 obtain ⟨href⟩ := RawMulLeftCongruence.ReflexivityProof.internalReflexivity n p old (RawMulNewestAddition.arithmetic a) x I.toCurrent.toComputation.toEvaluator.toAddition.toCongruence.toNewestEquality.toCongruences.toNewest ctx (addRaw I.consTag I.appendTag v t) index fuel
 have hself := Hilbert.Local.mp (.base href) htv
 obtain ⟨hreplace⟩ := RawMulNewestAddReplacements.StatementChecks.exactLeft n p old a x I ctx t u v index fuel
 have hrep := Hilbert.Local.mp (.mp (.mp (.base hreplace) ht) hu) hv
 obtain ⟨hmp1⟩ := LiteralCoreMP.StatementChecks.coreMP (RawMulLeftReplace.logicalLeaf (RawMulLeftCongruence.previousLogical old)) (RawMulNewestAddition.arithmetic a) x n p
  I.itag I.lengthTag I.appendTag I.pairTag I.consTag rightTag I.dropTag I.lookupTag I.dtag
  I.hi I.hlength I.ha I.hp I.hc hright I.hdrop I.hlookup I.hdispatcher I.mpTag I.qctag I.hmp I.hqc
  ctx .zero (eqRaw I.consTag I.appendTag t u) (intermediateRaw I.consTag I.appendTag t u v)
  (RawAddLeftCertificate.certificate I.consTag I.addLeftLineTag t u v) cert index fuel
 have hinputs1 : Hilbert.Local T ctx G (LiteralCoreMP.inputAcceptance I.qctag I.appendTag I.consTag .zero
  (eqRaw I.consTag I.appendTag t u) (intermediateRaw I.consTag I.appendTag t u v)
  (RawAddLeftCertificate.certificate I.consTag I.addLeftLineTag t u v) cert index fuel) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hrep) hinput
 have hfirst := Hilbert.Local.mp (.base hmp1) hinputs1
 obtain ⟨hmp2⟩ := LiteralCoreMP.StatementChecks.coreMP (RawMulLeftReplace.logicalLeaf (RawMulLeftCongruence.previousLogical old)) (RawMulNewestAddition.arithmetic a) x n p
  I.itag I.lengthTag I.appendTag I.pairTag I.consTag rightTag I.dropTag I.lookupTag I.dtag
  I.hi I.hlength I.ha I.hp I.hc hright I.hdrop I.hlookup I.hdispatcher I.mpTag I.qctag I.hmp I.hqc
  ctx .zero (selfRaw I.consTag I.appendTag t v) (outputRaw I.consTag I.appendTag t u v)
  (LiteralMPRun.certificate I.mpTag .zero (intermediateRaw I.consTag I.appendTag t u v)
   (RawAddLeftCertificate.certificate I.consTag I.addLeftLineTag t u v) cert)
  (RawCumulativeLogical.certificate I.consTag I.reflexivityTag (addRaw I.consTag I.appendTag v t)) index fuel
 have hinputs2 : Hilbert.Local T ctx G (LiteralCoreMP.inputAcceptance I.qctag I.appendTag I.consTag .zero
  (selfRaw I.consTag I.appendTag t v) (outputRaw I.consTag I.appendTag t u v)
  (LiteralMPRun.certificate I.mpTag .zero (intermediateRaw I.consTag I.appendTag t u v)
   (RawAddLeftCertificate.certificate I.consTag I.addLeftLineTag t u v) cert)
  (RawCumulativeLogical.certificate I.consTag I.reflexivityTag (addRaw I.consTag I.appendTag v t)) index fuel) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hfirst) hself
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
  (Hilbert.Local.discharge (Hilbert.Local.discharge (.mp (.base hmp2) hinputs2)))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddCongruences.LeftProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddCongruences.LeftProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddCongruences.LeftProof.internalCongruence
