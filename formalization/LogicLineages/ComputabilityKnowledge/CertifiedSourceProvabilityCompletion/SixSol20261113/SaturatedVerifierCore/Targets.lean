module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierCore.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierCore.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
/-- The actual bounded-search wrapper accepts iff its actual original core
accepts at that SAME bound. Explicit actual copies may be installed at different
tags, bridged by registry coherence. No abstract core-monotonicity, bounded-run,
Boolean-range, native calibration, source identity or syntax premise is given.
The internal core monotonicity must be derived for this literal saturated-leaf
core; the existential fuel witness is internal, not externally enumerated. -/
def InternalEquivalence : Prop :=
 ∀ (valid logical arithmetic : Program 1) (x : Program 3),
 ∀ n (p : Program n) (vtag qtag : Nat),
 (nodes p)[vtag]? = some ⟨5,LiteralKernelSource.verifier valid logical arithmetic
   (SaturatedAxiomLeaf.saturated x) LiteralCheckerAuxiliaries.bound
   LiteralCheckerAuxiliaries.initial LiteralCheckerAuxiliaries.finalizer⟩ →
 (nodes p)[qtag]? = some ⟨5,LiteralKernelSource.coreChecker valid logical arithmetic
   (SaturatedAxiomLeaf.saturated x) LiteralCheckerAuxiliaries.bound
   LiteralCheckerAuxiliaries.initial LiteralCheckerAuxiliaries.finalizer⟩ →
 ∀ ctx (index fuel context formula certificate : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (equivalence vtag qtag index fuel context formula certificate))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierCore.Targets
