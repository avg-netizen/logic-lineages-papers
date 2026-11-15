module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Every encoded packed state and replacement, without successful-scan, list
image, or tuple-shape premise. Actual pair surjectivity/destructor laws pay any
necessary decomposition internally. Empty remaining input is identity on both. -/
def InternalTickErasure : Prop := ∀ n (p : Program n) (etag ntag otag : Nat),
 (nodes p)[etag]? = some ⟨1,eraseCode⟩ →
 (nodes p)[ntag]? = some ⟨2,UniformClosedSubstitutionFold.tick⟩ →
 (nodes p)[otag]? = some ⟨1,LiteralSyntaxScan.tick⟩ →
 ∀ ctx (state raw : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (eraseCall etag (newTickCall ntag state raw))
   (oldTickCall otag (eraseCall etag state))))
/-- All symbolic counts, packed states, and replacement terms. No native count
or list witnesses; genuine internal PA iterator simulation is required. -/
def InternalIteratorErasure : Prop := ∀ n (p : Program n) (etag ntag otag : Nat),
 (nodes p)[etag]? = some ⟨1,eraseCode⟩ →
 (nodes p)[ntag]? = some ⟨3,UniformClosedSubstitutionFold.iterator⟩ →
 (nodes p)[otag]? = some ⟨2,LiteralSyntaxScan.iterator⟩ →
 ∀ ctx (count state raw : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (eraseCall etag (UniformClosedSubstitutionFold.iterateCall ntag count state raw))
   (LiteralSyntaxScan.Iteration.runCall otag count (eraseCall etag state))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.Targets
