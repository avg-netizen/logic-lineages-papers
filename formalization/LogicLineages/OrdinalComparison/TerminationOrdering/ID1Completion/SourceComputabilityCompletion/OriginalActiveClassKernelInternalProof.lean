module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalActiveClassKernel OriginalActiveClassKernelTargets
open OriginalActiveClassKernelEqualityProof OriginalActiveClassKernelBranchProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Usable internal characterization under a derived original seed domain. -/
theorem characterizationAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (O : Program 1) (P : Program 3) (seed candidate parameter : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (Domain p H G W seed parameter))) :
    Nonempty (Derivation body Delta
      ((Accepted p H G W O P seed candidate parameter).iff
        (Matrix p H G W O seed candidate parameter))) := by
  let A := Accepted p H G W O P seed candidate parameter
  let B := Matrix p H G W O seed candidate parameter
  obtain ⟨hf⟩ := matrixFromRelation p H G W O P seed candidate parameter
    (withHyp hd A) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := relationFromMatrix p H G W O P seed candidate parameter
    (withHyp hd B) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem hitDomainAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (O : Program 1) (P : Program 3) (seed candidate parameter : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (Domain p H G W seed parameter)))
    (hr : Nonempty (Derivation body Delta (Accepted p H G W O P seed candidate parameter))) :
    Nonempty (Derivation body Delta (Domain p H G W candidate parameter)) :=
  andLeft (matrixFromRelation p H G W O P seed candidate parameter hd hr)

theorem rowForwardAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (O : Program 1) (P : Program 3) (seed other probe parameter : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (Domain p H G W seed parameter)))
    (ho : Nonempty (Derivation body Delta (Accepted p H G W O P seed other parameter)))
    (hp : Nonempty (Derivation body Delta (Accepted p H G W O P seed probe parameter))) :
    Nonempty (Derivation body Delta (Accepted p H G W O P other probe parameter)) := by
  have mo := matrixFromRelation p H G W O P seed other parameter hd ho
  have mp := matrixFromRelation p H G W O P seed probe parameter hd hp
  exact relationFromMatrix p H G W O P other probe parameter (andLeft mo)
    (andIntro (andLeft mp)
      (andIntro
        (keyRowForward p.base.oldRepresentative seed other probe parameter
          (andLeft (andRight mo)) (andLeft (andRight mp)))
        (observerRowForward O seed other probe parameter
          (andRight (andRight mo)) (andRight (andRight mp)))))

theorem rowBackwardAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (O : Program 1) (P : Program 3) (seed other probe parameter : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (Domain p H G W seed parameter)))
    (ho : Nonempty (Derivation body Delta (Accepted p H G W O P seed other parameter)))
    (hp : Nonempty (Derivation body Delta (Accepted p H G W O P other probe parameter))) :
    Nonempty (Derivation body Delta (Accepted p H G W O P seed probe parameter)) := by
  have mo := matrixFromRelation p H G W O P seed other parameter hd ho
  have mp := matrixFromRelation p H G W O P other probe parameter (andLeft mo) hp
  exact relationFromMatrix p H G W O P seed probe parameter hd
    (andIntro (andLeft mp)
      (andIntro
        (keyRowBackward p.base.oldRepresentative seed other probe parameter
          (andLeft (andRight mo)) (andLeft (andRight mp)))
        (observerRowBackward O seed other probe parameter
          (andRight (andRight mo)) (andRight (andRight mp)))))

theorem rowCoherenceAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (O : Program 1) (P : Program 3) (seed other probe parameter : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (Domain p H G W seed parameter)))
    (ho : Nonempty (Derivation body Delta (Accepted p H G W O P seed other parameter))) :
    Nonempty (Derivation body Delta
      ((Accepted p H G W O P seed probe parameter).iff
        (Accepted p H G W O P other probe parameter))) := by
  let A := Accepted p H G W O P seed probe parameter
  let B := Accepted p H G W O P other probe parameter
  obtain ⟨hf⟩ := rowForwardAt p H G W O P seed other probe parameter
    (withHyp hd A) (withHyp ho A) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := rowBackwardAt p H G W O P seed other probe parameter
    (withHyp hd B) (withHyp ho B) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem actualOriginalActiveClassKernelCharacterization :
    ActualOriginalActiveClassKernelCharacterization := by
  intro p H G W O P positive alpha Delta seed candidate parameter
  obtain ⟨h⟩ := characterizationAt (body := positive)
    (Delta := Domain p H G W seed parameter :: Delta)
    p H G W O P seed candidate parameter ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualOriginalActiveClassKernelHitDomain : ActualOriginalActiveClassKernelHitDomain := by
  intro p H G W O P positive alpha Delta seed candidate parameter
  let A := Domain p H G W seed parameter ⊓ Accepted p H G W O P seed candidate parameter
  have h : Nonempty (Derivation positive (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hout⟩ := hitDomainAt p H G W O P seed candidate parameter (andLeft h) (andRight h)
  exact ⟨Derivation.implicationIntroduction hout⟩

theorem actualOriginalActiveClassKernelRowCoherence :
    ActualOriginalActiveClassKernelRowCoherence := by
  intro p H G W O P positive alpha Delta seed other probe parameter
  let A := Domain p H G W seed parameter ⊓ Accepted p H G W O P seed other parameter
  have h : Nonempty (Derivation positive (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hout⟩ := rowCoherenceAt p H G W O P seed other probe parameter (andLeft h) (andRight h)
  exact ⟨Derivation.implicationIntroduction hout⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelInternalProof
