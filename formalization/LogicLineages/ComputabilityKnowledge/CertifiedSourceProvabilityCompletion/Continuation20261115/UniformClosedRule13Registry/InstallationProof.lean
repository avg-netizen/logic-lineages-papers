module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Registry.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Registry.InstallationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Structural helper at the ACTUAL root. Every witness comes from its nodes;
no tag chosen in another root, runtime acceptance or image is assumed. -/
theorem installed (old arithmetic : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (hall : ∀ q ∈ items old arithmetic x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (UniformClosedRule13Certificate.Installation p old arithmetic x) := by
 obtain ⟨caseTag,h_caseTag⟩ := hall (⟨1,UniformClosedCase13.caseCode⟩ : Packed) (by simp [items])
 obtain ⟨predTag,h_predTag⟩ := hall (⟨1,HistoryCodec.predecessor⟩ : Packed) (by simp [items])
 obtain ⟨itag,h_itag⟩ := hall (⟨2,UniformClosedInstanceRecognizer.instanceCode⟩ : Packed) (by simp [items])
 obtain ⟨ftag,h_ftag⟩ := hall (⟨3,UniformClosedSubstitutionRawFold.foldCode⟩ : Packed) (by simp [items])
 obtain ⟨fval,h_fval⟩ := hall (⟨2,LiteralSyntaxValidator.formulaValidator⟩ : Packed) (by simp [items])
 obtain ⟨vtag,h_vtag⟩ := hall (⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ : Packed) (by simp [items])
 obtain ⟨ptag,h_ptag⟩ := hall (⟨2,HistoryCodec.pair⟩ : Packed) (by simp [items])
 obtain ⟨ctag,h_ctag⟩ := hall (⟨2,HistoryCodec.cons⟩ : Packed) (by simp [items])
 obtain ⟨rtag,h_rtag⟩ := hall (⟨1,HistoryDecoder.decoder true⟩ : Packed) (by simp [items])
 obtain ⟨len,h_len⟩ := hall (⟨1,HistoryLengthOffset.lengthProgram⟩ : Packed) (by simp [items])
 obtain ⟨htag,h_htag⟩ := hall (⟨1,HistoryLookup.head⟩ : Packed) (by simp [items])
 obtain ⟨ttag,h_ttag⟩ := hall (⟨1,HistoryLookup.tail⟩ : Packed) (by simp [items])
 obtain ⟨atag,h_atag⟩ := hall (⟨2,HistoryAppend.append⟩ : Packed) (by simp [items])
 obtain ⟨etag,h_etag⟩ := hall (⟨3,UniformClosedSubstitutionEmit.emitCode⟩ : Packed) (by simp [items])
 obtain ⟨stepTag,h_stepTag⟩ := hall (⟨2,LiteralSyntaxStep.stepCode⟩ : Packed) (by simp [items])
 obtain ⟨stag,h_stag⟩ := hall (⟨2,LiteralSyntaxScan.scanCode⟩ : Packed) (by simp [items])
 obtain ⟨dtag,h_dtag⟩ := hall (⟨2,HistoryCodec.difference⟩ : Packed) (by simp [items])
 obtain ⟨qtag,h_qtag⟩ := hall (⟨2,HistoryLookup.lookup⟩ : Packed) (by simp [items])
 obtain ⟨ltag,h_ltag⟩ := hall (⟨1,HistoryDecoder.decoder false⟩ : Packed) (by simp [items])
 obtain ⟨constructorTag,h_constructor⟩ := hall (⟨2,UniformClosedRule13.lineConstructor⟩ : Packed) (by simp [items])
 obtain ⟨lineTag,h_line⟩ := hall (⟨1,LiteralSyntaxValidator.lineValidator⟩ : Packed) (by simp [items])
 obtain ⟨logicalTag,h_logical⟩ := hall (⟨1,UniformClosedRule13.logicalLeaf old⟩ : Packed) (by simp [items])
 obtain ⟨dispatcherTag,h_dispatcher⟩ := hall (⟨4,UniformClosedRule13Dispatcher.dispatcher old arithmetic x⟩ : Packed) (by simp [items])
 obtain ⟨iteratorTag,h_iterator⟩ := hall (⟨4,SixSol20261112.HistoryMachine.iterator (UniformClosedRule13Certificate.kernel old arithmetic x)⟩ : Packed) (by simp [items])
 obtain ⟨coreTag,h_core⟩ := hall (⟨5,UniformClosedRule13Certificate.checker old arithmetic x⟩ : Packed) (by simp [items])
 obtain ⟨verifierTag,h_verifier⟩ := hall (⟨5,UniformClosedRule13Certificate.verifier old arithmetic x⟩ : Packed) (by simp [items])
 let graph : UniformClosedRule13Validity.GraphInstallation p :=
  { caseTag,predTag,itag,ftag,fval,vtag,ptag,ctag,rtag,len,htag,ttag,atag,h_caseTag,h_predTag,h_itag,h_ftag,h_fval,h_vtag,h_ptag,h_ctag,h_rtag,h_len,h_htag,h_ttag,h_atag }
 let validity : UniformClosedRule13Validity.Installation p :=
  { toGraphInstallation := graph, etag,stepTag,stag,dtag,qtag,ltag,h_etag,h_stepTag,h_stag,h_dtag,h_qtag,h_ltag }
 let dispatch : UniformClosedRule13Dispatcher.Installation p old arithmetic x :=
  { toInstallation := validity, constructorTag,lineTag,logicalTag,dispatcherTag,h_constructor,h_line,h_logical,h_dispatcher }
 exact ⟨{ toDispatcherInstallation := dispatch, iteratorTag,coreTag,verifierTag,h_iterator,h_core,h_verifier }⟩
/-- Actual subtree admission with globally recovered tags; reusable beneath a
future published root, without any Theory(carrier) inclusion assertion. -/
theorem installedAt (old arithmetic : Program 1) (x : Program 3) {n : Nat} (p : Program n) (tag : Nat)
 (ht : (nodes p)[tag]? = some ⟨6,carrier old arithmetic x⟩) :
 Nonempty (UniformClosedRule13Certificate.Installation p old arithmetic x) :=
 installed old arithmetic x p
  (ReflexivityInstalled.BundleProof.bundleInstallation (items old arithmetic x) n p tag ht)
theorem finiteInstallation (old arithmetic : Program 1) (x : Program 3) :
 Nonempty (UniformClosedRule13Certificate.Installation (carrier old arithmetic x) old arithmetic x) :=
 installedAt old arithmetic x (carrier old arithmetic x) 0
  (GorbowPRRegistry.StatementChecks.rootTag 6 (carrier old arithmetic x))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Registry.InstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Registry.InstallationProof
