module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.InductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.SeedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceConjunctionProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (refl)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph

theorem internalSeedMembership : Targets.InternalSeedMembership := by
  intro E body alpha Delta count pool seed parameter out hr
  apply programCases InternalListCodec.consCode (Fin.cons seed (Fin.cons z Fin.elim0)) _
  intro beta j Theta singleton hj hs
  simp only [graph2Rename,numeral,sucRelabel,zRelabel]
  simp only [consTermRename,emptyRename,zRelabel] at hs
  have hr' := renameInto hr j Theta hj
  rw [graph4Rename] at hr'
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
  have he : Nonempty (Derivation body Theta (equal (seed.relabel j) (seed.relabel j))) := by
    rw [equalEqn]
    exact ⟨refl _⟩
  have hm := containsHit singleton (seed.relabel j) z (seed.relabel j) hs he
  exact InductionProof.internalPreservation E body beta Theta (count.relabel j) (pool.relabel j)
    singleton (parameter.relabel j) (out.relabel j) (seed.relabel j) hi hm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.SeedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.SeedProof
