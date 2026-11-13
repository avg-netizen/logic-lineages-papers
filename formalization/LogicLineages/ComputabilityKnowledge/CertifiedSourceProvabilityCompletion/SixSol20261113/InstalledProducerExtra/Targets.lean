module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.InstalledProducerExtra.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.InstalledProducerExtra.Targets
open GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB

/-- A NEW source tuple selected after installing CK, a structural container,
and the exact supplied extra AST. Original pG, not merely its container, is
installed. All retained source contracts refer to the same new pF,pR,q,c.
ProducerFor q pG is intentionally neither needed nor inferred here: callers
retain that independent semantic contract. No old/new tuple identity. -/
def ActualRegistryWithExtra : Prop := ∀ (q : Program 5), UniversalVerifier q →
 ∀ (pCK : Program 2), GorbowUniformCommonKnowledge.CodeProgram pCK →
 ∀ (pG : Program 6) (r : Nat) (extra : Program r),
 ∃ (pF pR : Program 1) (c : Code) (tagCK tagG tagExtra : Nat),
 Actual pF pR q c ∧ SourceBaseCompletion.SyntaxAdequate pF pR q ∧
 GorbowUniformCommonKnowledge.RegistryInstall pF pR q tagCK pCK ∧
 GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tagCK ∧
 InstalledProducer.RegistryInstall pF pR q tagG pG ∧
 (nodes (GorbowSourceRegistryPadding.root (augmented pF q) pR))[tagExtra]? = some ⟨r,extra⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.InstalledProducerExtra.Targets
