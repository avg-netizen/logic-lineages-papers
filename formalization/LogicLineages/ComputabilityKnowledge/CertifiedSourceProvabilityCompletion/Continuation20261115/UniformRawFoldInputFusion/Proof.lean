module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.InductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.Proof
/-- Exact original machine input concatenation, including arbitrary malformed
packed states and token codes; the generalized internal induction discharges
all raw reconstruction and changing-state premises. -/
theorem inputFusion : Targets.InternalInputFusion := by
 intro n p ftag etag stepTag ptag ctag atag ltag rtag hf he hs hp hc ha hl hr ctx left right packed replacement
 exact InductionProof.internalAll p ftag etag stepTag ptag ctag atag ltag rtag
  hf he hs hp hc ha hl hr left right replacement packed
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.Proof
