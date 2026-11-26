module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityComposition.ReflexivityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityComposition.CompositionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof
noncomputable def localTransport {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (G : List (Formula ctx)) (t u v first second index fuel : Term ctx)
 (ht : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.vtag t))
 (hu : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.vtag u))
 (hv : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.vtag v))
 (hfirst : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (accepted I.qctag I.ctag I.atag index fuel t u first))
 (hsecond : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (accepted I.qctag I.ctag I.atag index fuel t v second)) :
 Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.qctag I.ctag I.atag index fuel u v (transportCertificate I.mpTag I.qtag I.ctag I.atag t u v first second)) := by
 apply Classical.choice
 obtain ⟨hr⟩ := RawRightReplaceCertificate.StatementChecks.exactCore n p (RawCumulativeLogical.logical old) a x I.toRight ctx t u v index fuel
 have hrep := Hilbert.Local.mp (Hilbert.Local.mp (Hilbert.Local.mp (.base hr) ht) hu) hv
 let mid := LiteralRawMP.implicationRaw I.atag I.ctag (eqRaw I.ctag I.atag t v) (eqRaw I.ctag I.atag u v)
 let rc := RawRightReplaceCertificate.certificate I.ctag I.qtag t u v
 let mc := LiteralMPRun.certificate I.mpTag .zero mid rc first
 obtain ⟨hm1⟩ := LiteralCoreMP.StatementChecks.coreMP (RawRightReplace.logicalLeaf (RawCumulativeLogical.logical old)) a x n p
  I.itag I.lengthTag I.atag I.ptag I.ctag I.rightTag I.dropTag I.lookupTag I.dtag
  I.hi I.hlength I.ha I.hp I.hc I.hright I.hdrop I.hlookup I.hd I.mpTag I.qctag I.hmp I.hqc
  ctx .zero (eqRaw I.ctag I.atag t u) mid rc first index fuel
 have hs := Hilbert.Local.mp (.base hm1) (.mp (.mp (.base (.logical (.andIntro _ _))) hrep) hfirst)
 obtain ⟨hm2⟩ := LiteralCoreMP.StatementChecks.coreMP (RawRightReplace.logicalLeaf (RawCumulativeLogical.logical old)) a x n p
  I.itag I.lengthTag I.atag I.ptag I.ctag I.rightTag I.dropTag I.lookupTag I.dtag
  I.hi I.hlength I.ha I.hp I.hc I.hright I.hdrop I.hlookup I.hd I.mpTag I.qctag I.hmp I.hqc
  ctx .zero (eqRaw I.ctag I.atag t v) (eqRaw I.ctag I.atag u v) mc second index fuel
 exact ⟨.mp (.base hm2) (.mp (.mp (.base (.logical (.andIntro _ _))) hs) hsecond)⟩

theorem internalSymmetry : Targets.InternalSymmetry := by
 intro n p old a x I ctx t u cert index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid I.vtag t
 let W := RawReflexivityDispatcher.valid I.vtag u
 let A := accepted I.qctag I.ctag I.atag index fuel t u cert
 let G := [A,W,V]
 have ht : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 have hu : Hilbert.Local T ctx G W := .hypothesis (by simp [G])
 have hin : Hilbert.Local T ctx G A := .hypothesis List.mem_cons_self
 obtain ⟨hr⟩ := ReflexivityProof.internalReflexivity n p old a x I ctx t index fuel
 have href := Hilbert.Local.mp (.base hr) ht
 have hout := localTransport p old a x I G t u t cert (reflexivityCertificate I.ctag I.reflexivityTag t) index fuel ht hu ht hin href
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))⟩

theorem internalTransitivity : Targets.InternalTransitivity := by
 intro n p old a x I ctx t u v first second index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid I.vtag t
 let W := RawReflexivityDispatcher.valid I.vtag u
 let U := RawReflexivityDispatcher.valid I.vtag v
 let A := accepted I.qctag I.ctag I.atag index fuel t u first
 let B := accepted I.qctag I.ctag I.atag index fuel u v second
 let G := [B,A,U,W,V]
 have ht : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 have hu : Hilbert.Local T ctx G W := .hypothesis (by simp [G])
 have hv : Hilbert.Local T ctx G U := .hypothesis (by simp [G])
 have hf : Hilbert.Local T ctx G A := .hypothesis (by simp [G])
 have hs : Hilbert.Local T ctx G B := .hypothesis List.mem_cons_self
 obtain ⟨hsy⟩ := internalSymmetry n p old a x I ctx t u first index fuel
 have hreverse := Hilbert.Local.mp (Hilbert.Local.mp (Hilbert.Local.mp (.base hsy) ht) hu) hf
 have hout := localTransport p old a x I G u t v
  (symmetryCertificate I.mpTag I.qtag I.reflexivityTag I.ctag I.atag t u first) second index fuel hu ht hv hreverse hs
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge
  (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityComposition.CompositionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityComposition.CompositionProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityComposition.CompositionProof.localTransport
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityComposition.CompositionProof.internalSymmetry
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityComposition.CompositionProof.internalTransitivity
