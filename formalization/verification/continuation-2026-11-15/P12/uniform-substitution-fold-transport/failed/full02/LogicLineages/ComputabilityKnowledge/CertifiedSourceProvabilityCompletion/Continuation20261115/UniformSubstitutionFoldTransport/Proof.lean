module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.InductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.Proof
open GorbowSyntax GorbowTheoryProof SixSol20261113 InvariantProof
open UniformSubstitutionChunkTransport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Exact frozen whole-fold endpoint: empty initial output discharges the
internal prefix premise; no additional state/image/success premise survives. -/
theorem successfulFoldTransport : Targets.InternalSuccessfulFoldTransport := by
 intro n p ftag etag vtag stepTag stag ptag ctag atag dtag len q l r hf he hv hstep hs hp hc ha hd hlen hq hl hr ctx tokens oldTasks newTasks oldResult raw
 obtain ⟨h⟩ := InductionProof.internalAll p ftag etag vtag stepTag stag ptag ctag atag dtag len q l r hf he hv hstep hs hp hc ha hd hlen hq hl hr
  tokens newTasks raw oldTasks newTasks .zero oldResult
 obtain ⟨hnil⟩ := UniformSubstitutionChunkTransport.ScanProof.nil p stag ptag hs hp newTasks
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid vtag raw
 let R := stackRelation len q l r oldTasks newTasks
 let S := Formula.equal (LiteralSyntaxScan.scanCall stag oldTasks tokens) (.succ oldResult)
 let G := [S,R,V]
 have hvv : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 have hrel : Hilbert.Local T ctx G R := .hypothesis (by simp [G])
 have hold : Hilbert.Local T ctx G S := .hypothesis (by simp [G])
 have hout := Hilbert.Local.mp (.mp (.mp (.mp (.base h) hvv) hrel) (.base hnil)) hold
 exact ⟨hout.discharge.discharge.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.Proof
