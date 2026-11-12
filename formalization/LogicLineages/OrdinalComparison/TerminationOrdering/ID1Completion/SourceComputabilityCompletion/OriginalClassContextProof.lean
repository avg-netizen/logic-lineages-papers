module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumCoherenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph2)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalActiveClassKernel (Domain Accepted)
open OriginalActiveKernelMinimum OriginalActiveKernelMinimumSupportProof
open OriginalActiveKernelMinimumCoherenceProof OriginalActiveClassKernelInternalProof
open OriginalActiveClassKernelBranchProof
open UniformCertificateCompletion OriginalClassContextTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The two actual least hits share their middle value. Row transport through
that value reconstructs the ORIGINAL relation between the original seeds. -/
theorem sharedOutputAt (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (seed other out parameter : OTerm alpha)
    (hd : Nonempty (Derivation positive Delta (Domain p H G W seed parameter)))
    (he : Nonempty (Derivation positive Delta (Domain p H G W other parameter)))
    (hr : Nonempty (Derivation positive Delta
      (graph2 (inputs p H G W P).base.oldRepresentative out seed parameter)))
    (hs : Nonempty (Derivation positive Delta
      (graph2 (inputs p H G W P).base.oldRepresentative out other parameter))) :
    Nonempty (Derivation positive Delta
      (Accepted p H G W OriginalRawSyntaxTransport.variableRankPackedRaw P
        seed other parameter)) := by
  let O := OriginalRawSyntaxTransport.variableRankPackedRaw
  have hself := relationFromMatrix p H G W O P other other parameter he
    (matrixOfEqual p H G W O other other parameter he
      ⟨InternalTagArithmeticSupportProof.refl other⟩)
  have ha := minimumHit p H G W P seed out parameter hd hr
  have hb := minimumHit p H G W P other out parameter he hs
  have hc := rowForwardAt p H G W O P other out other parameter he hb hself
  exact rowBackwardAt p H G W O P seed out other parameter hd ha hc

theorem actualOriginalClassContextSharedOutput : ActualOriginalClassContextSharedOutput := by
  intro p H G W P positive alpha Delta seed other out parameter
  let R := (inputs p H G W P).base.oldRepresentative
  let A := Domain p H G W seed parameter ⊓
    (Domain p H G W other parameter ⊓
      (graph2 R out seed parameter ⊓ graph2 R out other parameter))
  have h : Nonempty (Derivation positive (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hc⟩ := sharedOutputAt p H G W P seed other out parameter
    (andLeft h) (andLeft (andRight h))
    (andLeft (andRight (andRight h))) (andRight (andRight (andRight h)))
  exact ⟨Derivation.implicationIntroduction hc⟩

theorem outputEquivalenceAt (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (seed other out otherOut parameter : OTerm alpha)
    (hd : Nonempty (Derivation positive Delta (Domain p H G W seed parameter)))
    (he : Nonempty (Derivation positive Delta (Domain p H G W other parameter)))
    (hr : Nonempty (Derivation positive Delta
      (graph2 (inputs p H G W P).base.oldRepresentative out seed parameter)))
    (hs : Nonempty (Derivation positive Delta
      (graph2 (inputs p H G W P).base.oldRepresentative otherOut other parameter))) :
    Nonempty (Derivation positive Delta
      ((equal out otherOut).iff
        (Accepted p H G W OriginalRawSyntaxTransport.variableRankPackedRaw P
          seed other parameter))) := by
  let R := (inputs p H G W P).base.oldRepresentative
  let E := equal out otherOut
  let C := Accepted p H G W OriginalRawSyntaxTransport.variableRankPackedRaw P
    seed other parameter
  have hEq : Derivation positive (E :: Delta) E := Derivation.hypothesis List.mem_cons_self
  change Derivation positive (E :: Delta) (equal out otherOut) at hEq
  rw [equal,InternalSourceInversionSupportProof.onEquality] at hEq
  have hs' : Nonempty (Derivation positive (E :: Delta)
      (graph2 R out other parameter)) :=
    InternalControlGraphSupportProof.outputTransport R otherOut out
      (Fin.cons other (Fin.cons parameter Fin.elim0))
      ⟨InternalTagArithmeticSupportProof.symm hEq⟩ (withHyp hs E)
  obtain ⟨hf⟩ := sharedOutputAt p H G W P seed other out parameter
    (withHyp hd E) (withHyp he E) (withHyp hr E) hs'
  obtain ⟨hb⟩ := coherenceAt p H G W P seed other out otherOut parameter
    (withHyp hd C) ⟨Derivation.hypothesis List.mem_cons_self⟩
    (withHyp hr C) (withHyp hs C)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem actualOriginalClassContextOutputEquivalence :
    ActualOriginalClassContextOutputEquivalence := by
  intro p H G W P positive alpha Delta seed other out otherOut parameter
  let R := (inputs p H G W P).base.oldRepresentative
  let A := Domain p H G W seed parameter ⊓
    (Domain p H G W other parameter ⊓
      (graph2 R out seed parameter ⊓ graph2 R otherOut other parameter))
  have h : Nonempty (Derivation positive (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hc⟩ := outputEquivalenceAt p H G W P seed other out otherOut parameter
    (andLeft h) (andLeft (andRight h))
    (andLeft (andRight (andRight h))) (andRight (andRight (andRight h)))
  exact ⟨Derivation.implicationIntroduction hc⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextProof
