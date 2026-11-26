module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationRegistry.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationRegistry.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Structural membership extraction, reusable only when the actual root's
memberships have themselves been proved. No tags are identified across roots. -/
theorem installed (f : Formula 1) (old arithmetic : Program 1) (x : Program 3)
 {n : Nat} (p : Program n)
 (hall : ∀ q ∈ items f old arithmetic x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (FullFormulaInstantiationCertificate.Installation p f old arithmetic x) := by
 obtain ⟨qtag,hq⟩ := hall (⟨1,FullFormulaInstantiation.line f⟩ : Packed) (by simp [items])
 obtain ⟨ptag,hp⟩ := hall (⟨2,HistoryCodec.pair⟩ : Packed) (by simp [items])
 obtain ⟨ctag,hc⟩ := hall (⟨2,HistoryCodec.cons⟩ : Packed) (by simp [items])
 obtain ⟨atag,ha⟩ := hall (⟨2,HistoryAppend.append⟩ : Packed) (by simp [items])
 obtain ⟨vtag,hv⟩ := hall (⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ : Packed) (by simp [items])
 obtain ⟨ftag,hf⟩ := hall (⟨2,LiteralSyntaxValidator.formulaValidator⟩ : Packed) (by simp [items])
 obtain ⟨ltag,hl⟩ := hall (⟨1,LiteralSyntaxValidator.lineValidator⟩ : Packed) (by simp [items])
 obtain ⟨btag,hb⟩ := hall (⟨1,FullFormulaInstantiation.logicalLeaf f old⟩ : Packed) (by simp [items])
 obtain ⟨dtag,hd⟩ := hall (⟨4,FullFormulaInstantiationDispatcher.dispatcher f old arithmetic x⟩ : Packed) (by simp [items])
 obtain ⟨itag,hi⟩ := hall (⟨4,SixSol20261112.HistoryMachine.iterator (FullFormulaInstantiationCertificate.kernel f old arithmetic x)⟩ : Packed) (by simp [items])
 obtain ⟨qctag,hqc⟩ := hall (⟨5,FullFormulaInstantiationCertificate.checker f old arithmetic x⟩ : Packed) (by simp [items])
 obtain ⟨utag,hu⟩ := hall (⟨5,FullFormulaInstantiationCertificate.verifier f old arithmetic x⟩ : Packed) (by simp [items])
 let previous : FullFormulaInstantiationDispatcher.Installation p f old arithmetic x :=
  { qtag,ptag,ctag,atag,vtag,ftag,ltag,btag,dtag,hq,hp,hc,ha,hv,hf,hl,hb,hd }
 exact ⟨{ toInstallation := previous, itag,qctag,utag,hi,hqc,hu }⟩
/-- Noncircular explicit carrier: first build ASTs, then recover their tags. -/
theorem finiteInstallation : Targets.FiniteInstallation := by
 intro f old arithmetic x
 let p := carrier f old arithmetic x
 have hall : ∀ q ∈ items f old arithmetic x, ∃ tag : Nat, (nodes p)[tag]? = some q :=
  ReflexivityInstalled.BundleProof.bundleInstallation (items f old arithmetic x) 6 p 0
   (GorbowPRRegistry.StatementChecks.rootTag 6 p)
 exact installed f old arithmetic x p hall
/-- All three actual runtime capabilities share this one chosen installation. -/
theorem oneRuntimePackage : Targets.OneRuntimePackage := by
 intro f old arithmetic x
 obtain ⟨I⟩ := finiteInstallation f old arithmetic x
 refine ⟨I, ?_⟩
 intro ctx raw index fuel
 let p := carrier f old arithmetic x
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid I.vtag raw
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hrun⟩ := FullFormulaInstantiationCertificate.StatementChecks.exactInternalSingletonRun
  f 6 p old arithmetic x I ctx raw index fuel
 obtain ⟨hcore⟩ := FullFormulaInstantiationCertificate.StatementChecks.exactInternalCore
  f 6 p old arithmetic x I ctx raw index fuel
 obtain ⟨hfuel⟩ := FullFormulaInstantiationCertificate.StatementChecks.exactInternalFuel
  f 6 p old arithmetic x I ctx raw index fuel
 have a := Hilbert.Local.mp (Hilbert.Local.base hrun) hh
 have b := Hilbert.Local.mp (Hilbert.Local.base hcore) hh
 have c := Hilbert.Local.mp (Hilbert.Local.base hfuel) hh
 have bc := Hilbert.Local.mp (Hilbert.Local.mp (Hilbert.Local.base (.logical (.andIntro _ _))) b) c
 have abc := Hilbert.Local.mp (Hilbert.Local.mp (Hilbert.Local.base (.logical (.andIntro _ _))) a) bc
 exact ⟨abc.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationRegistry.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationRegistry.Proof
