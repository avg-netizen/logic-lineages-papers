module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionAcceptedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumRowProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open UniformCertificateCompletion
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open OriginalAllPositionMinimumCoherenceTargets
open OriginalAllPositionAcceptedProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rowAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (seed other candidate parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain p H G W seed parameter)))
 (hh : Nonempty (Derivation body Delta (Accepted p H G W P seed other parameter))) :
 Nonempty (Derivation body Delta ((Accepted p H G W P seed candidate parameter).iff
   (Accepted p H G W P other candidate parameter))) := by
 have exposed := acceptedRecover p H G W P seed other parameter hd hh
 have otherDomain := actualHitDomain p H G W P body alpha Delta seed other parameter hd hh
 have kernel := OriginalActiveClassKernelInternalProof.rowCoherenceAt p H G W
   OriginalRawSyntaxTransport.variableRankPackedRaw P seed other candidate parameter hd (andLeft exposed)
 have tests := OriginalAllPositionRelationTestsProof.allTestsRow p.base.oldRepresentative
   seed other candidate parameter (andRight exposed)
 let A := Accepted p H G W P seed candidate parameter
 let B := Accepted p H G W P other candidate parameter
 have forward : Nonempty (Derivation body (A :: Delta) B) := by
   have parts := acceptedRecover p H G W P seed candidate parameter (withHyp hd A)
     (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
   exact acceptedIntro p H G W P other candidate parameter (withHyp otherDomain A)
     (iffForward (withHyp kernel A) (andLeft parts)) (iffForward (withHyp tests A) (andRight parts))
 have backward : Nonempty (Derivation body (B :: Delta) A) := by
   have parts := acceptedRecover p H G W P other candidate parameter (withHyp otherDomain B)
     (show Nonempty (Derivation body (B :: Delta) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
   exact acceptedIntro p H G W P seed candidate parameter (withHyp hd B)
     (iffBackward (withHyp kernel B) (andLeft parts)) (iffBackward (withHyp tests B) (andRight parts))
 obtain ⟨hf⟩ := forward
 obtain ⟨hb⟩ := backward
 exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

theorem actualRowCoherence : RowCoherence := by
 intro p H G W P body alpha Delta seed other candidate parameter
 let A := OriginalActiveClassKernel.Domain p H G W seed parameter ⊓ Accepted p H G W P seed other parameter
 have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨result⟩ := rowAt p H G W P seed other candidate parameter (andLeft h) (andRight h)
 exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumRowProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumRowProof
