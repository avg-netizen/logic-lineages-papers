module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumCoherenceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph2)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalBetaTotalityProof (addHyp)
open OriginalActiveClassKernel (Domain Accepted)
open OriginalActiveKernelMinimum OriginalActiveKernelMinimumTargets
open OriginalActiveKernelMinimumSupportProof OriginalActiveClassKernelInternalProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Equal actual acceptance rows and genuine least-hit minimality force
the same selected output, even though the two scans use different bounds. -/
theorem coherenceAt (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (seed other out otherOut parameter : OTerm alpha)
    (hd : Nonempty (Derivation positive Delta (Domain p H G W seed parameter)))
    (hc : Nonempty (Derivation positive Delta
      (Accepted p H G W OriginalRawSyntaxTransport.variableRankPackedRaw P
        seed other parameter)))
    (hr : Nonempty (Derivation positive Delta
      (graph2 (inputs p H G W P).base.oldRepresentative out seed parameter)))
    (hs : Nonempty (Derivation positive Delta
      (graph2 (inputs p H G W P).base.oldRepresentative otherOut other parameter))) :
    Nonempty (Derivation positive Delta (equal out otherOut)) := by
  have hother := hitDomainAt p H G W OriginalRawSyntaxTransport.variableRankPackedRaw P
    seed other parameter hd hc
  have hm := minimumFacts p H G W P seed out parameter otherOut hd hr
  have hn := minimumFacts p H G W P other otherOut parameter out hother hs
  obtain ⟨hmOther⟩ := rowForwardAt p H G W OriginalRawSyntaxTransport.variableRankPackedRaw P
    seed other out parameter hd hc (andLeft (andRight hm))
  obtain ⟨hnSeed⟩ := rowBackwardAt p H G W OriginalRawSyntaxTransport.variableRankPackedRaw P
    seed other otherOut parameter hd hc (andLeft (andRight hn))
  obtain ⟨hmMiss⟩ := andRight (andRight hm)
  obtain ⟨hnMiss⟩ := andRight (andRight hn)
  have hforward : Nonempty (Derivation positive Delta
      (InternalLessThan.strictLess out otherOut).not) := by
    exact ⟨Derivation.implicationIntroduction
      (Derivation.implicationElimination
        (Derivation.implicationElimination (addHyp hnMiss _)
          (Derivation.hypothesis List.mem_cons_self)) (addHyp hmOther _))⟩
  have hbackward : Nonempty (Derivation positive Delta
      (InternalLessThan.strictLess otherOut out).not) := by
    exact ⟨Derivation.implicationIntroduction
      (Derivation.implicationElimination
        (Derivation.implicationElimination (addHyp hmMiss _)
          (Derivation.hypothesis List.mem_cons_self)) (addHyp hnSeed _))⟩
  exact equalOfNotLess out otherOut hforward hbackward

theorem actualOriginalActiveKernelMinimumCoherence :
    ActualOriginalActiveKernelMinimumCoherence := by
  intro p H G W P positive alpha Delta seed other out otherOut parameter
  let R := (inputs p H G W P).base.oldRepresentative
  let A := Domain p H G W seed parameter ⊓
    (Accepted p H G W OriginalRawSyntaxTransport.variableRankPackedRaw P seed other parameter ⊓
      (graph2 R out seed parameter ⊓ graph2 R otherOut other parameter))
  have h : Nonempty (Derivation positive (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨he⟩ := coherenceAt p H G W P seed other out otherOut parameter
    (andLeft h) (andLeft (andRight h))
    (andLeft (andRight (andRight h))) (andRight (andRight (andRight h)))
  exact ⟨Derivation.implicationIntroduction he⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumCoherenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumCoherenceProof
