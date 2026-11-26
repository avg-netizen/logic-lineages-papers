module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAddition.ArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAddition.StepProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
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
 obtain ⟨hab⟩ := RawAdditionComputation.ValidityProof.internalAdditionValidity n p I.vtag I.ptag I.ctag I.atag I.hv I.hp I.hc I.ha ctx t u
 have hvab := Hilbert.Local.mp (Hilbert.Local.mp (.base hab) ht) hu
 obtain ⟨hsu⟩ := RawSuccCongruence.ValidityProof.internalSuccessorValidity n p I.vtag I.ptag I.ctag I.hv I.hp I.hc ctx u
 have hvsu := Hilbert.Local.mp (.base hsu) hu
 obtain ⟨hasu⟩ := RawAdditionComputation.ValidityProof.internalAdditionValidity n p I.vtag I.ptag I.ctag I.atag I.hv I.hp I.hc I.ha ctx t (succRaw I.ctag u)
 have hvasu := Hilbert.Local.mp (Hilbert.Local.mp (.base hasu) ht) hvsu
 obtain ⟨hsab⟩ := RawSuccCongruence.ValidityProof.internalSuccessorValidity n p I.vtag I.ptag I.ctag I.hv I.hp I.hc ctx (addRaw I.ctag I.atag t u)
 have hvsab := Hilbert.Local.mp (.base hsab) hvab
 obtain ⟨hsv⟩ := RawSuccCongruence.ValidityProof.internalSuccessorValidity n p I.vtag I.ptag I.ctag I.hv I.hp I.hc ctx v
 have hvsv := Hilbert.Local.mp (.base hsv) hv
 obtain ⟨har⟩ := ArithmeticProof.additionAxiom p old a x I t u index fuel
 have harith := Hilbert.Local.mp (Hilbert.Local.mp (.base har) ht) hu
 obtain ⟨hcon⟩ := RawRetainedSuccCongruence.StatementChecks.exactCoreCongruence n p old (arithmetic a) x
  I.toCongruence ctx (addRaw I.ctag I.atag t u) v cert index fuel
 have hcong := Hilbert.Local.mp (Hilbert.Local.mp (Hilbert.Local.mp (.base hcon) hvab) hv) hin
 obtain ⟨htr⟩ := RawEqualityComposition.StatementChecks.exactTransitivity n p old (arithmetic a) x
  I.toCongruence.toEquality ctx (addRaw I.ctag I.atag t (succRaw I.ctag u))
  (succRaw I.ctag (addRaw I.ctag I.atag t u)) (succRaw I.ctag v)
  (RawAddSuccCertificate.certificate I.ctag I.addTag t u)
  (RawSuccCongruence.certificate I.mpTag I.replaceTag I.reflexivityTag I.ctag I.atag (addRaw I.ctag I.atag t u) v cert) index fuel
 have hout := Hilbert.Local.mp (Hilbert.Local.mp (Hilbert.Local.mp (Hilbert.Local.mp (Hilbert.Local.mp
  (.base htr) hvasu) hvsab) hvsv) harith) hcong
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
  (Hilbert.Local.discharge (Hilbert.Local.discharge hout))))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAddition.StepProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAddition.StepProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAddition.StepProof.internalStep
