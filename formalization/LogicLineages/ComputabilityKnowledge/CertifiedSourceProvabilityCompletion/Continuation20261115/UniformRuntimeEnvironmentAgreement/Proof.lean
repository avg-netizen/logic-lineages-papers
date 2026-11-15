module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.FormulaProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.Proof
/-- Exact frozen endpoint: all original installed programs predate the chosen
formula/environment, and private expansion membership is recovered at the same
root. No replacement validator or generated-certificate assumption is added. -/
theorem runtimeEnvironmentAgreement : Targets.InternalRuntimeEnvironmentAgreement := by
 intro arity p ftag etag vtag stepTag stag ptag ctag atag dtag len q l r
  hf he hv hst hs hp hc ha hd hlen hq hl hr n depth inputs e f ctx G raw replacement rest out hinputs
 obtain ⟨xtag,hx⟩ := RelationalSyntaxDepthTransport.ClosedScanInstallationProof.expandNode p stepTag hst
 let I : UniformFixedFormulaAgreement.Traversal.Installation p :=
  { ftag := ftag, ptag := ptag, ctag := ctag, stag := stepTag, etag := etag,
    atag := atag, xtag := xtag, dtag := dtag, ltag := l, rtag := r,
    hf := hf, hp := hp, hc := hc, hs := hst, he := he, ha := ha,
    hx := hx, hd := hd, hl := hl, hr := hr }
 obtain ⟨h⟩ := FormulaProof.traverses p I vtag stag len q hv hs hlen hq G e raw replacement hinputs f rest out
 exact ⟨by simpa only [agreement,initial,MachineProof.run,I] using h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.Proof
