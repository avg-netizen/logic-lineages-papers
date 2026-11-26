module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestTransitivity.ReplacementProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestTransitivity.CompositionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open RawEqualityComposition
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof
noncomputable def localTransport {n ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (G : List (Formula ctx)) (t u v first second index fuel : Term ctx)
 (ht : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.validatorTag t))
 (hu : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.validatorTag u))
 (hv : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.validatorTag v))
 (hfirst : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (accepted I.qctag I.consTag I.appendTag index fuel t u first))
 (hsecond : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (accepted I.qctag I.consTag I.appendTag index fuel t v second)) :
 Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.qctag I.consTag I.appendTag index fuel u v (transportCertificate I.mpTag I.equalityLineTag I.consTag I.appendTag t u v first second)) := by
 apply Classical.choice
 obtain ⟨scanTag,hscan⟩ := TwoSol20261113.ReflexivityRecognizer.TermInternalProof.scanInstalled p I.validatorTag I.hv
 obtain ⟨_,_,_,rightTag,_,_,_,hright⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p scanTag hscan
 obtain ⟨hr⟩ := ReplacementProof.internalReplacement n p old a x I ctx t u v index fuel
 have hrep := Hilbert.Local.mp (Hilbert.Local.mp (Hilbert.Local.mp (.base hr) ht) hu) hv
 let mid := LiteralRawMP.implicationRaw I.appendTag I.consTag (eqRaw I.consTag I.appendTag t v) (eqRaw I.consTag I.appendTag u v)
 let rc := RawRightReplaceCertificate.certificate I.consTag I.equalityLineTag t u v
 let mc := LiteralMPRun.certificate I.mpTag .zero mid rc first
 obtain ⟨hm1⟩ := LiteralCoreMP.StatementChecks.coreMP (RawAddLeftReplace.logicalLeaf (RawAddLeftCongruence.previousLogical old)) a x n p
  I.itag I.lengthTag I.appendTag I.pairTag I.consTag rightTag I.dropTag I.lookupTag I.dtag
  I.hi I.hlength I.ha I.hp I.hc hright I.hdrop I.hlookup I.hdispatcher I.mpTag I.qctag I.hmp I.hqc
  ctx .zero (eqRaw I.consTag I.appendTag t u) mid rc first index fuel
 have hs := Hilbert.Local.mp (.base hm1) (.mp (.mp (.base (.logical (.andIntro _ _))) hrep) hfirst)
 obtain ⟨hm2⟩ := LiteralCoreMP.StatementChecks.coreMP (RawAddLeftReplace.logicalLeaf (RawAddLeftCongruence.previousLogical old)) a x n p
  I.itag I.lengthTag I.appendTag I.pairTag I.consTag rightTag I.dropTag I.lookupTag I.dtag
  I.hi I.hlength I.ha I.hp I.hc hright I.hdrop I.hlookup I.hdispatcher I.mpTag I.qctag I.hmp I.hqc
  ctx .zero (eqRaw I.consTag I.appendTag t v) (eqRaw I.consTag I.appendTag u v) mc second index fuel
 exact ⟨.mp (.base hm2) (.mp (.mp (.base (.logical (.andIntro _ _))) hs) hsecond)⟩

theorem internalSymmetry : ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u cert index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag u)
    (.imp (accepted I.qctag I.consTag I.appendTag index fuel t u cert)
     (accepted I.qctag I.consTag I.appendTag index fuel u t
      (symmetryCertificate I.mpTag I.equalityLineTag I.reflexivityTag I.consTag I.appendTag t u cert)))))) := by
 intro n p old a x I ctx t u cert index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid I.validatorTag t
 let W := RawReflexivityDispatcher.valid I.validatorTag u
 let A := accepted I.qctag I.consTag I.appendTag index fuel t u cert
 let G := [A,W,V]
 have ht : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 have hu : Hilbert.Local T ctx G W := .hypothesis (by simp [G])
 have hin : Hilbert.Local T ctx G A := .hypothesis List.mem_cons_self
 obtain ⟨hr⟩ := RawAddLeftCongruence.ReflexivityProof.internalReflexivity n p old a x I.toCongruences.toNewest ctx t index fuel
 have href := Hilbert.Local.mp (.base hr) ht
 have hout := localTransport p old a x I G t u t cert (reflexivityCertificate I.consTag I.reflexivityTag t) index fuel ht hu ht hin href
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))⟩

theorem internalTransitivity : Targets.InternalTransitivity := by
 intro n p old a x I ctx t u v first second index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid I.validatorTag t
 let W := RawReflexivityDispatcher.valid I.validatorTag u
 let U := RawReflexivityDispatcher.valid I.validatorTag v
 let A := accepted I.qctag I.consTag I.appendTag index fuel t u first
 let B := accepted I.qctag I.consTag I.appendTag index fuel u v second
 let G := [B,A,U,W,V]
 have ht : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 have hu : Hilbert.Local T ctx G W := .hypothesis (by simp [G])
 have hv : Hilbert.Local T ctx G U := .hypothesis (by simp [G])
 have hf : Hilbert.Local T ctx G A := .hypothesis (by simp [G])
 have hs : Hilbert.Local T ctx G B := .hypothesis List.mem_cons_self
 obtain ⟨hsy⟩ := internalSymmetry n p old a x I ctx t u first index fuel
 have hreverse := Hilbert.Local.mp (Hilbert.Local.mp (Hilbert.Local.mp (.base hsy) ht) hu) hf
 have hout := localTransport p old a x I G u t v
  (symmetryCertificate I.mpTag I.equalityLineTag I.reflexivityTag I.consTag I.appendTag t u first) second index fuel hu ht hv hreverse hs
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge
  (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestTransitivity.CompositionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestTransitivity.CompositionProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestTransitivity.CompositionProof.localTransport
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestTransitivity.CompositionProof.internalSymmetry
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestTransitivity.CompositionProof.internalTransitivity
