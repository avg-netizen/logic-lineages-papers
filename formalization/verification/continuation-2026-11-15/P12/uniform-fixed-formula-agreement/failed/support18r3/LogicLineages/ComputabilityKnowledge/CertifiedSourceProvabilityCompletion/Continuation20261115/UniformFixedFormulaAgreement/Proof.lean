module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.FormulaProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.PrefixCodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph
/-- Original endpoint: all auxiliary tags are recovered internally; only the
fourteen original memberships and original validity guard remain in its type. -/
theorem agreement : Targets.InternalAgreement := by
 intro n p ftag etag vtag fval stepTag stag ptag ctag atag dtag len q l r
  hf he hv hstep hs hp hc ha hd hlen hq hl hr hfv f ctx raw
 obtain ⟨xtag,hx⟩ := RelationalSyntaxDepthTransport.ClosedScanInstallationProof.expandNode p stepTag hstep
 let I : Traversal.Installation p :=
  {ftag:=ftag,ptag:=ptag,ctag:=ctag,stag:=stepTag,etag:=etag,atag:=atag,xtag:=xtag,
   dtag:=dtag,ltag:=l,rtag:=r,hf:=hf,hp:=hp,hc:=hc,hs:=hstep,he:=he,ha:=ha,hx:=hx,hd:=hd,hl:=hl,hr:=hr}
 let state : Term ctx := .succ (LiteralSyntaxValidator.FormulaBindingProof.taskList ptag ctag (.succ .zero))
 let packed := HistoryKernel.pairCall ptag state (.zero : Term ctx)
 let value := FullFormulaInstantiation.instanceValue ctag atag f raw
 obtain ⟨htraverse⟩ := FormulaProof.traverses p I 0 f raw (.zero : Term ctx) .zero
 have htraverse' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedSubstitutionRawFold.foldCall ftag
   (SegmentProof.tokenPrefix ctag (GorbowFormulaPrefixCode.encode f) .zero) packed raw)
   (HistoryKernel.pairCall ptag (.succ .zero) (HistoryAppend.appendCall atag .zero value))) := by
  simpa only [EnvironmentProof.atZero] using htraverse
 obtain ⟨hcode⟩ := PrefixCodeProof.encoded p ctag hc (GorbowFormulaPrefixCode.encode f) (ctx := ctx)
 have hcng := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) ftag
  (SegmentProof.tokenPrefix ctag (GorbowFormulaPrefixCode.encode f) .zero ::ᵥ packed ::ᵥ raw ::ᵥ nil)
  (Term.numeral (FullFormulaInstantiation.templateCode f) ::ᵥ packed ::ᵥ raw ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact hcode
   | succ i => cases i using Fin.cases with
     | zero => exact .logical (.reflexive packed)
     | succ i => cases i using Fin.cases with
       | zero => exact .logical (.reflexive raw)
       | succ i => exact Fin.elim0 i)
 have hfold := Logic.trans _ _ _ (Support.equalitySymmetry _ _ hcng) htraverse'
 have hproject := HistoryLookup.DestructorProof.unaryCallCongruence r _ _ hfold
 obtain ⟨hdecode⟩ := HistoryLookup.DestructorProof.decoderCrossPair p r ptag true hr hp
  (.succ (.zero : Term ctx)) (HistoryAppend.appendCall atag .zero value)
 obtain ⟨hnil⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx value
 have heq : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (uniformValue ftag ptag ctag r f raw) value) :=
  Logic.trans _ _ _ hproject (Logic.trans _ _ _ hdecode hnil)
 have hlocal : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx
  [Continuation20261114.RawReflexivityDispatcher.valid vtag raw]
  (.equal (uniformValue ftag ptag ctag r f raw) value) := .base heq
 exact ⟨hlocal.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.Proof
