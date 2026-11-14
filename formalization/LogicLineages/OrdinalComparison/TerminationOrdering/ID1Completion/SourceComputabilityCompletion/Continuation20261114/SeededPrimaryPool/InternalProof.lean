module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SeededPrimaryPool.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.RunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.FilterStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.CutoffProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SeededPrimaryPool.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalTagArithmeticSupportProof SourceComputabilityFormulaSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open PrimaryMonotonicity.InclusionProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open TwoSol20261113.CalibratedPrimary.MembershipInternalProof

theorem poolCons (T Q : Program 2) (seed parameter code tail : OTerm alpha)
    (hT : Nonempty (Derivation body Delta (graph2 T (suc z) seed parameter)))
    (hQ : Nonempty (Derivation body Delta (graph2 Q tail seed parameter)))
    (hP : Nonempty (Derivation body Delta (graph2 (pool T Q) code seed parameter))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code seed tail)) := by
  have hc := successorBranchElim T (InternalAcceptance.constantZero 2)
    (.composition InternalListCodec.consCode ![.projection 0,Q]) code z ![seed,parameter] hT hP
  exact binaryRecover InternalListCodec.consCode (.projection 0) Q code seed tail ![seed,parameter]
    hc (projectionValue 0 ![seed,parameter]) hQ

theorem internalSeedInPool : Targets.InternalSeedInPool := by
  intro T Q body alpha Delta seed parameter code hT hP
  apply programCases Q (Fin.cons seed (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta tail hj hQ
  simp only [graph2Rename,numeral,sucRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at hQ
  have hT' := renameInto hT j Theta hj
  simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hT'
  have hP' := renameInto hP j Theta hj
  rw [graph2Rename] at hP'
  have hc := poolCons T Q (seed.relabel j) (parameter.relabel j) (code.relabel j) tail hT' hQ hP'
  apply containsHit (code.relabel j) (seed.relabel j) tail (seed.relabel j) hc
  rw [equalEqn]
  exact ⟨refl _⟩

theorem internalPoolCharacterization : Targets.InternalPoolCharacterization := by
  intro T Q body alpha Delta seed parameter code tail candidate hT hQ hP
  have hc := poolCons T Q seed parameter code tail hT hQ hP
  constructor
  · intro hm
    let A := equal seed candidate
    apply formulaCases A
    · have he : Nonempty (Derivation body (A :: Delta) (equal seed candidate)) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      rw [equalEqn] at he
      obtain ⟨he⟩ := he
      exact ⟨orLeft (symm he)⟩
    · obtain ⟨ht⟩ := PrimaryMembership.Proof.missRecover code seed tail candidate (suc z)
        (withHyp hc A.not) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hm A.not)
      exact ⟨orRight ht⟩
  · rintro ⟨hd⟩
    let A := eqn candidate seed
    have he : Nonempty (Derivation body (A :: Delta) (equal seed candidate)) := by
      rw [equalEqn]
      exact ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩
    obtain ⟨hl⟩ := containsHit code seed tail candidate (withHyp hc A) he
    let B := graph2 contains (suc z) tail candidate
    obtain ⟨hr⟩ := PrimaryEdgeInclusion.FilterStepProof.consContainsTail code seed tail candidate
      (withHyp hc B) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨disjunctionElimination hd (Derivation.implicationIntroduction hl)
      (Derivation.implicationIntroduction hr)⟩

theorem internalPrimaryCarrier : Targets.InternalPrimaryCarrier := by
  intro T Q E body alpha Delta seed parameter code out hT hP hL
  let P := pool T Q
  apply programCases (LengthAlignedPrimary.countOfPool P) (Fin.cons seed (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta size hj hc
  rw [includedRename]
  simp only [consTermRename,emptyRename] at hc
  have hT' := renameInto hT j Theta hj
  simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hT'
  have hP' := renameInto hP j Theta hj
  rw [graph2Rename] at hP'
  have hL' := renameInto hL j Theta hj
  rw [graph2Rename] at hL'
  let s := seed.relabel j
  let p := parameter.relabel j
  have hm := internalSeedInPool T Q body beta Theta s p (code.relabel j) hT' hP'
  have hr := successorBranchElim T (InternalAcceptance.constantZero 2)
    (.composition (PrimaryIteration.run E) ![LengthAlignedPrimary.countOfPool P,P,.projection 0,.projection 1])
    (out.relabel j) z ![s,p] hT' hL'
  have hi : Nonempty (Derivation body Theta
      (graph4 (PrimaryIteration.run E) (out.relabel j) size (code.relabel j) s p)) := by
    apply compositionRecover (PrimaryIteration.run E)
      ![LengthAlignedPrimary.countOfPool P,P,.projection 0,.projection 1]
      (out.relabel j) ![s,p] ![size,code.relabel j,s,p] hr
    intro i
    exact Fin.cases hc (Fin.cases hP' (Fin.cases (projectionValue 0 ![s,p])
      (Fin.cases (projectionValue 1 ![s,p]) (fun k => Fin.elim0 k)))) i
  exact PrimaryCarrierBound.RunProof.runIncludedInPool E body beta Theta size (code.relabel j)
    s p (out.relabel j) hi hm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SeededPrimaryPool.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SeededPrimaryPool.InternalProof
