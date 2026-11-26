module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidateInstallation.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidateInstallation.PoolProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalQuotientComparisonProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open TwoSol20261113.CalibratedPrimary
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem forwardAt
    (n : Nat) (arity : Fin n → Nat) (H G : Program 1)
    (seed parameter out candidate tail : OTerm alpha)
    (hT : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.target H G) (numeral 1) seed parameter)))
    (hP : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target H G)
      (candidateProgram n arity H)) out seed parameter)))
    (hQ : Nonempty (Derivation body Delta (graph2 (candidateProgram n arity H) tail seed parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 Membership.contains (numeral 1) out candidate))) :
    Nonempty (Derivation body Delta (eqn candidate seed ⊔ (OriginalClassCodes.Targets.meaning n arity H seed parameter candidate ⊓
      OriginalCandidates.Targets.retained H seed parameter candidate))) := by
  have hs := (SeededPrimaryPool.InternalProof.internalPoolCharacterization
    (OriginalTypedDecoder.target H G) (candidateProgram n arity H) body alpha Delta
    seed parameter out tail candidate hT hQ hP).mp hm
  apply OriginalTypedDecoderInternalBranchProof.orCases hs
  · exact ⟨orLeft (Derivation.hypothesis List.mem_cons_self)⟩
  · have ht : Nonempty (Derivation body
        (graph2 Membership.contains (numeral 1) tail candidate :: Delta)
        (graph2 Membership.contains (numeral 1) tail candidate)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hc⟩ := (OriginalCandidates.Proof.internalMembership n arity H body alpha _
      seed parameter tail candidate (withHyp hQ _)).mp ht
    exact ⟨orRight hc⟩

theorem backwardAt
    (n : Nat) (arity : Fin n → Nat) (H G : Program 1)
    (seed parameter out candidate tail : OTerm alpha)
    (hT : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.target H G) (numeral 1) seed parameter)))
    (hP : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target H G)
      (candidateProgram n arity H)) out seed parameter)))
    (hQ : Nonempty (Derivation body Delta (graph2 (candidateProgram n arity H) tail seed parameter)))
    (hm : Nonempty (Derivation body Delta (eqn candidate seed ⊔ (OriginalClassCodes.Targets.meaning n arity H seed parameter candidate ⊓
      OriginalCandidates.Targets.retained H seed parameter candidate)))) :
    Nonempty (Derivation body Delta (graph2 Membership.contains (numeral 1) out candidate)) := by
  apply (SeededPrimaryPool.InternalProof.internalPoolCharacterization
    (OriginalTypedDecoder.target H G) (candidateProgram n arity H) body alpha Delta
    seed parameter out tail candidate hT hQ hP).mpr
  apply OriginalTypedDecoderInternalBranchProof.orCases hm
  · exact ⟨orLeft (Derivation.hypothesis List.mem_cons_self)⟩
  · have hc : Nonempty (Derivation body
        ((OriginalClassCodes.Targets.meaning n arity H seed parameter candidate ⊓
          OriginalCandidates.Targets.retained H seed parameter candidate) :: Delta)
        (OriginalClassCodes.Targets.meaning n arity H seed parameter candidate ⊓
          OriginalCandidates.Targets.retained H seed parameter candidate)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨ht⟩ := (OriginalCandidates.Proof.internalMembership n arity H body alpha _
      seed parameter tail candidate (withHyp hQ _)).mpr hc
    exact ⟨orRight ht⟩

theorem forward
    (n : Nat) (arity : Fin n → Nat) (H G : Program 1)
    (seed parameter out candidate : OTerm alpha)
    (hT : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.target H G) (numeral 1) seed parameter)))
    (hP : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target H G)
      (candidateProgram n arity H)) out seed parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 Membership.contains (numeral 1) out candidate))) :
    Nonempty (Derivation body Delta ((eqn candidate seed ⊔ (OriginalClassCodes.Targets.meaning n arity H seed parameter candidate ⊓
      OriginalCandidates.Targets.retained H seed parameter candidate)))) := by
  apply InternalAcceptanceSupportProof.programCases (candidateProgram n arity H) ![seed,parameter] _
  intro beta j Theta tail hj hQ
  have hx : (fun i => (![seed,parameter] i).relabel j) =
      (![seed.relabel j,parameter.relabel j] : Fin 2 → OTerm beta) := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hQ
  have ht := renameInto hT j Theta hj
  have hp := renameInto hP j Theta hj
  have hh := renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at ht hp
  simp only [InternalBetaBoundaryProof.supRename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,
    eqnRelabel,conjunctionRename,OriginalClassCodes.MeaningRenameProof.meaningRename,
    OriginalCandidates.RetainedSyntaxProof.retainedRename] at hh ⊢
  exact forwardAt n arity H G (seed.relabel j) (parameter.relabel j) (out.relabel j)
    (candidate.relabel j) tail ht hp hQ hh

theorem backward
    (n : Nat) (arity : Fin n → Nat) (H G : Program 1)
    (seed parameter out candidate : OTerm alpha)
    (hT : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.target H G) (numeral 1) seed parameter)))
    (hP : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target H G)
      (candidateProgram n arity H)) out seed parameter)))
    (hm : Nonempty (Derivation body Delta ((eqn candidate seed ⊔ (OriginalClassCodes.Targets.meaning n arity H seed parameter candidate ⊓
      OriginalCandidates.Targets.retained H seed parameter candidate))))) :
    Nonempty (Derivation body Delta (graph2 Membership.contains (numeral 1) out candidate)) := by
  apply InternalAcceptanceSupportProof.programCases (candidateProgram n arity H) ![seed,parameter] _
  intro beta j Theta tail hj hQ
  have hx : (fun i => (![seed,parameter] i).relabel j) =
      (![seed.relabel j,parameter.relabel j] : Fin 2 → OTerm beta) := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hQ
  have ht := renameInto hT j Theta hj
  have hp := renameInto hP j Theta hj
  have hh := renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at ht hp
  simp only [InternalBetaBoundaryProof.supRename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,
    eqnRelabel,conjunctionRename,OriginalClassCodes.MeaningRenameProof.meaningRename,
    OriginalCandidates.RetainedSyntaxProof.retainedRename] at hh ⊢
  exact backwardAt n arity H G (seed.relabel j) (parameter.relabel j) (out.relabel j)
    (candidate.relabel j) tail ht hp hQ hh

theorem internalPoolMembership : Targets.InternalPoolMembership := by
  intro n arity H G body alpha Delta seed parameter out candidate ht hp
  exact ⟨forward n arity H G seed parameter out candidate ht hp,
    backward n arity H G seed parameter out candidate ht hp⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidateInstallation.PoolProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidateInstallation.PoolProof
