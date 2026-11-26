module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionComputation.ValidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionComputation.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
def baseInstallation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) : RawCumulativeArithmetic.CertificateInstallation p (RawRightReplace.logicalLeaf (RawCumulativeLogical.logical old)) a x := {
 qtag := I.zeroTag, ptag := I.ptag, ctag := I.ctag, atag := I.atag,
 vtag := I.vtag, ftag := I.ftag, ltag := I.ltag, btag := I.arithmeticTag,
 dtag := I.dtag, itag := I.itag, qctag := I.qctag, utag := I.utag,
 hq := I.hzero, hp := I.hp, hc := I.hc, ha := I.ha,
 hv := I.hv, hf := I.hf, hl := I.hl, hb := I.harithmetic,
 hd := I.hd, hi := I.hi, hqc := I.hqc, hu := I.hu }

def stepInstallation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) : RawAddSuccCertificate.Installation p (RawRightReplace.logicalLeaf (RawCumulativeLogical.logical old)) (RawAddZero.arithmeticLeaf a) x := {
 qtag := I.addTag, ptag := I.ptag, ctag := I.ctag, atag := I.atag,
 vtag := I.vtag, ftag := I.ftag, ltag := I.ltag, btag := I.arithmeticTag,
 dtag := I.dtag, itag := I.itag, qctag := I.qctag, utag := I.utag,
 hq := I.hadd, hp := I.hp, hc := I.hc, ha := I.ha,
 hv := I.hv, hf := I.hf, hl := I.hl, hb := I.harithmetic,
 hd := I.hd, hi := I.hi, hqc := I.hqc, hu := I.hu }

theorem internalBase : Targets.InternalBase := by
 intro n p old a x I ctx t index fuel
 exact RawCumulativeArithmetic.StatementChecks.exactCore n p
  (RawRightReplace.logicalLeaf (RawCumulativeLogical.logical old)) a x
  (baseInstallation p old a x I) ctx t index fuel

theorem internalStep : Targets.InternalStep := by
 intro n p old a x I ctx t u v cert index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid I.vtag t
 let W := RawReflexivityDispatcher.valid I.vtag u
 let U := RawReflexivityDispatcher.valid I.vtag v
 let A := RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel (addRaw I.ctag I.atag t u) v cert
 let G := [A,U,W,V]
 have ht : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 have hu : Hilbert.Local T ctx G W := .hypothesis (by simp [G])
 have hv : Hilbert.Local T ctx G U := .hypothesis (by simp [G])
 have hin : Hilbert.Local T ctx G A := .hypothesis List.mem_cons_self
 obtain ⟨hab⟩ := ValidityProof.internalAdditionValidity n p I.vtag I.ptag I.ctag I.atag I.hv I.hp I.hc I.ha ctx t u
 have hvab := Hilbert.Local.mp (Hilbert.Local.mp (.base hab) ht) hu
 obtain ⟨hsu⟩ := RawSuccCongruence.ValidityProof.internalSuccessorValidity n p I.vtag I.ptag I.ctag I.hv I.hp I.hc ctx u
 have hvsu := Hilbert.Local.mp (.base hsu) hu
 obtain ⟨hasu⟩ := ValidityProof.internalAdditionValidity n p I.vtag I.ptag I.ctag I.atag I.hv I.hp I.hc I.ha ctx t (succRaw I.ctag u)
 have hvasu := Hilbert.Local.mp (Hilbert.Local.mp (.base hasu) ht) hvsu
 obtain ⟨hsab⟩ := RawSuccCongruence.ValidityProof.internalSuccessorValidity n p I.vtag I.ptag I.ctag I.hv I.hp I.hc ctx (addRaw I.ctag I.atag t u)
 have hvsab := Hilbert.Local.mp (.base hsab) hvab
 obtain ⟨hsv⟩ := RawSuccCongruence.ValidityProof.internalSuccessorValidity n p I.vtag I.ptag I.ctag I.hv I.hp I.hc ctx v
 have hvsv := Hilbert.Local.mp (.base hsv) hv
 obtain ⟨har⟩ := RawAddSuccCertificate.StatementChecks.exactCore n p
  (RawRightReplace.logicalLeaf (RawCumulativeLogical.logical old)) (RawAddZero.arithmeticLeaf a) x
  (stepInstallation p old a x I) ctx t u index fuel
 have harith := Hilbert.Local.mp (Hilbert.Local.mp (.base har) ht) hu
 obtain ⟨hcon⟩ := RawRetainedSuccCongruence.StatementChecks.exactCoreCongruence n p old (RawCumulativeArithmetic.arithmetic a) x
  I.toCongruence ctx (addRaw I.ctag I.atag t u) v cert index fuel
 have hcong := Hilbert.Local.mp (Hilbert.Local.mp (Hilbert.Local.mp (.base hcon) hvab) hv) hin
 obtain ⟨htr⟩ := RawEqualityComposition.StatementChecks.exactTransitivity n p old (RawCumulativeArithmetic.arithmetic a) x
  I.toCongruence.toEquality ctx (addRaw I.ctag I.atag t (succRaw I.ctag u))
  (succRaw I.ctag (addRaw I.ctag I.atag t u)) (succRaw I.ctag v)
  (RawAddSuccCertificate.certificate I.ctag I.addTag t u)
  (RawSuccCongruence.certificate I.mpTag I.replaceTag I.reflexivityTag I.ctag I.atag (addRaw I.ctag I.atag t u) v cert) index fuel
 have hout := Hilbert.Local.mp (Hilbert.Local.mp (Hilbert.Local.mp (Hilbert.Local.mp (Hilbert.Local.mp
  (.base htr) hvasu) hvsab) hvsv) harith) hcong
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
  (Hilbert.Local.discharge (Hilbert.Local.discharge hout))))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionComputation.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionComputation.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionComputation.Proof.internalBase
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionComputation.Proof.internalStep
