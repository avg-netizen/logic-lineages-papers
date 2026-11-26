module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCheckerSuccessCertificate.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalSource
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
/-- Chosen BEFORE verifier/source construction; not a post-selection root cast. -/
abbrev selectedOld (rawOld : Program 1) : Program 1 :=
 OriginalQuantifierLogicalExtension.logicalLeaf rawOld
/-- Exact additional syntax, independent of selected source/index/addresses. -/
def items (rawOld : Program 1) : List Packed :=
 [⟨2,OriginalQuantifierLogicalProducers.lineConstructor false⟩,
  ⟨2,OriginalQuantifierLogicalProducers.lineConstructor true⟩,
  ⟨2,OriginalQuantifierLogicalProducers.singletonConstructor false⟩,
  ⟨2,OriginalQuantifierLogicalProducers.singletonConstructor true⟩,
  ⟨1,OriginalQuantifierLogicalExtension.recognizer false⟩,
  ⟨1,OriginalQuantifierLogicalExtension.recognizer true⟩,
  ⟨1,selectedOld rawOld⟩]
def extra {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (rawOld a : Program 1) (baseX : Program 3) : Program 6 :=
 let old := selectedOld rawOld
 let Q : Program 1 → Program 1 → Program 3 → Program 5 :=
  fun old a baseX => CumulativePropositionalSource.verifier f lhs rhs old a baseX
 ReflexivityInstalled.bundle
  (⟨6,CurrentStructuralProducerSource.extendedExtra f lhs rhs t Q old a baseX⟩ :: items rawOld)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalSource
