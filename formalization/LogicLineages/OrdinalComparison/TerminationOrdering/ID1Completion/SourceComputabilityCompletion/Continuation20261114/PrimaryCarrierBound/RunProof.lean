module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.InductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InclusionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.RunProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceConjunctionProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open PrimaryIteration (iterate run)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph


variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem singletonMember (singleton seed candidate : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleton seed z)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) singleton candidate))) :
    Nonempty (Derivation body Delta (eqn candidate seed)) := by
  let A := equal seed candidate
  apply formulaCases A
  · have h : Nonempty (Derivation body (A :: Delta) (equal seed candidate)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    rw [equalEqn] at h
    obtain ⟨h⟩ := h
    exact ⟨symm h⟩
  · have hn := PrimaryMembership.Proof.missRecover singleton seed z candidate (suc z)
      (withHyp hs A.not) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hm A.not)
    obtain ⟨hu⟩ := valueUnique contains (suc z) z ![z,candidate] hn (containsNil candidate)
    exact ⟨Derivation.explosion (sucNeZeroApply hu)⟩

theorem runCarrier : Targets.RunCarrier := by
  intro E body alpha Delta count pool seed parameter out candidate hr hm
  apply programCases InternalListCodec.consCode (Fin.cons seed (Fin.cons z Fin.elim0)) _
  intro beta j Theta singleton hj hs
  simp only [PrimaryExpansionSoundness.AppendSyntaxProof.orRename,eqnRelabel,graph2Rename,numeral,sucRelabel,zRelabel]
  simp only [consTermRename,emptyRename,zRelabel] at hs
  have hr' := renameInto hr j Theta hj
  rw [graph4Rename] at hr'
  have hm' := renameInto hm j Theta hj
  simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hm'
  let xs : Fin 4 → OTerm beta := ![count.relabel j,pool.relabel j,seed.relabel j,parameter.relabel j]
  let singletonP : Program 4 := .composition InternalListCodec.consCode
    ![.projection 2,InternalAcceptance.constantZero 4]
  have hsingle := binaryValue InternalListCodec.consCode (.projection 2)
    (InternalAcceptance.constantZero 4) singleton (seed.relabel j) z xs hs
    (projectionValue 2 xs) (constantZeroValue xs)
  have hi : Nonempty (Derivation body Theta
      (graph4 (iterate E) (out.relabel j) (count.relabel j) (pool.relabel j) singleton (parameter.relabel j))) := by
    apply compositionRecover (iterate E) ![.projection 0,.projection 1,singletonP,.projection 3]
      (out.relabel j) xs ![count.relabel j,pool.relabel j,singleton,parameter.relabel j] hr'
    intro i
    exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
      (Fin.cases hsingle (Fin.cases (projectionValue 3 xs) (fun k => Fin.elim0 k)))) i
  obtain ⟨hd⟩ := InductionProof.iterationCarrier E body beta Theta (count.relabel j)
    (pool.relabel j) singleton (parameter.relabel j) (out.relabel j) (candidate.relabel j) hi hm'
  let A := graph2 contains (suc z) singleton (candidate.relabel j)
  obtain ⟨he⟩ := singletonMember singleton (seed.relabel j) (candidate.relabel j)
    (withHyp hs A) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination hd (Derivation.implicationIntroduction (orLeft he))
    (Derivation.implicationIntroduction (orRight (Derivation.hypothesis List.mem_cons_self)))⟩

theorem poolMember (pool seed candidate : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 contains (suc z) pool seed)))
    (he : Nonempty (Derivation body Delta (eqn candidate seed))) :
    Nonempty (Derivation body Delta (graph2 contains (suc z) pool candidate)) := by
  obtain ⟨he⟩ := he
  unfold graph2 programGraph at hp ⊢
  apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 Delta
    (OrdinaryArithmetic.graphFormula contains) (suc z) ![pool,seed] ![pool,candidate] _ hp
  intro i
  simp only [InternalSourceInversionSupportProof.onEquality]
  exact Fin.cases (Nonempty.intro (refl pool))
    (Fin.cases (Nonempty.intro (symm he)) (fun k => Fin.elim0 k)) i

theorem runIncludedInPool : Targets.RunIncludedInPool := by
  intro E body alpha Delta count pool seed parameter out hr hp
  apply PrimaryMonotonicity.InclusionProof.introduce out pool
  intro beta j Theta candidate hj hm
  have hr' := renameInto hr j Theta hj
  rw [graph4Rename] at hr'
  have hp' := renameInto hp j Theta hj
  simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hp'
  obtain ⟨hd⟩ := runCarrier E body beta Theta (count.relabel j) (pool.relabel j)
    (seed.relabel j) (parameter.relabel j) (out.relabel j) candidate hr' hm
  let A := eqn candidate (seed.relabel j)
  obtain ⟨hl⟩ := poolMember (pool.relabel j) (seed.relabel j) candidate
    (withHyp hp' A) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination hd (Derivation.implicationIntroduction hl)
    (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.RunProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.RunProof
