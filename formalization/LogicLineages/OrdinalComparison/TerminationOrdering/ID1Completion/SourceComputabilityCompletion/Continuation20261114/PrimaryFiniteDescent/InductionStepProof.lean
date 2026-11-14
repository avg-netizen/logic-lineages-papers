module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.InductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.RecursionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.InductionStepProof
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

open InductionDefinitions.Induction InductionSyntaxProof
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalAdditionLawsProof InternalOriginalOrderSyntaxProof
open PrimaryMonotonicity.InclusionProof PrimaryIteration.RecursionProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem rowApply (E : Program 3)
    (elapsed pool initial parameter out next initialRemaining remaining : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (AtCount E elapsed)))
    (hi : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) out elapsed pool initial parameter)))
    (he : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand E) next pool out parameter)))
    (hinit : Nonempty (Derivation body Delta (graph2 PrimaryUncoveredCount.count initialRemaining pool initial)))
    (hrem : Nonempty (Derivation body Delta (graph2 PrimaryUncoveredCount.count remaining pool out))) :
    Nonempty (Derivation body Delta (budget elapsed initialRemaining remaining out next)) := by
  obtain ⟨h⟩ := elimination body alpha 7 Delta (matrix E elapsed)
    (fun i => emb (![pool,initial,parameter,out,next,initialRemaining,remaining] i)) hrow
  rw [InductionSyntaxProof.matrixWitness] at h
  obtain ⟨hf⟩ := andIntro hi (andIntro he (andIntro hinit hrem))
  exact ⟨Derivation.implicationElimination h hf⟩

theorem zeroCore (E : Program 3)
    (pool initial parameter out next initialRemaining remaining : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) out z pool initial parameter)))
    (hinit : Nonempty (Derivation body Delta (graph2 PrimaryUncoveredCount.count initialRemaining pool initial)))
    (hrem : Nonempty (Derivation body Delta (graph2 PrimaryUncoveredCount.count remaining pool out))) :
    Nonempty (Derivation body Delta (budget z initialRemaining remaining out next)) := by
  have he := valueUnique (PrimaryIteration.iterate E) out initial ![z,pool,initial,parameter]
    hi (zeroValue E pool initial parameter)
  have hr : Nonempty (Derivation body Delta
      (graph2 PrimaryUncoveredCount.count remaining pool initial)) := by
    unfold graph2 programGraph at hrem ⊢
    apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 Delta
      (OrdinaryArithmetic.graphFormula PrimaryUncoveredCount.count) remaining ![pool,out] ![pool,initial] _ hrem
    intro i
    simp only [InternalSourceInversionSupportProof.onEquality]
    exact Fin.cases (Nonempty.intro (refl pool)) (Fin.cases he (fun k => Fin.elim0 k)) i
  obtain ⟨hu⟩ := valueUnique PrimaryUncoveredCount.count remaining initialRemaining ![pool,initial] hr hinit
  exact ⟨orRight (orRight (trans (leftZero remaining) hu))⟩

theorem successorKnown (E : Program 3)
    (elapsed pool initial parameter out next initialRemaining remaining previous previousRemaining : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (AtCount E elapsed)))
    (hp : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) previous elapsed pool initial parameter)))
    (hstep : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand E) out pool previous parameter)))
    (he : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand E) next pool out parameter)))
    (hinit : Nonempty (Derivation body Delta (graph2 PrimaryUncoveredCount.count initialRemaining pool initial)))
    (hrem : Nonempty (Derivation body Delta (graph2 PrimaryUncoveredCount.count remaining pool out)))
    (hprev : Nonempty (Derivation body Delta (graph2 PrimaryUncoveredCount.count previousRemaining pool previous))) :
    Nonempty (Derivation body Delta (budget (suc elapsed) initialRemaining remaining out next)) := by
  obtain ⟨hold⟩ := rowApply E elapsed pool initial parameter previous out initialRemaining previousRemaining
    hrow hp hstep hinit hprev
  let S := PrimaryMonotonicity.included out previous
  let B := PrimaryUncoveredCount.bounded (add elapsed previousRemaining) initialRemaining
  have hs : Nonempty (Derivation body (S :: Delta) (budget (suc elapsed) initialRemaining remaining out next)) := by
    obtain ⟨h⟩ := PrimaryStability.InclusionProof.successorStability E body alpha (S :: Delta)
      pool previous out next parameter (withHyp hstep S) (withHyp he S)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨orLeft h⟩
  have hb : Nonempty (Derivation body (B :: Delta) (budget (suc elapsed) initialRemaining remaining out next)) := by
    obtain ⟨hcase⟩ := StepProof.stepAlternative E body alpha (B :: Delta)
      pool previous out parameter previousRemaining remaining (withHyp hstep B)
      (withHyp hprev B) (withHyp hrem B)
    obtain ⟨hs'⟩ := PrimaryStability.InclusionProof.successorStability E body alpha (S :: B :: Delta)
      pool previous out next parameter (withHyp (withHyp hstep B) S) (withHyp (withHyp he B) S)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    let L := ltF remaining previousRemaining
    obtain ⟨hb'⟩ := ArithmeticProof.budgetStep (body := body) (Delta := L :: B :: Delta)
      elapsed previousRemaining remaining initialRemaining ⟨Derivation.hypothesis List.mem_cons_self⟩
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    exact ⟨disjunctionElimination hcase (Derivation.implicationIntroduction (orLeft hs'))
      (Derivation.implicationIntroduction (orRight hb'))⟩
  obtain ⟨hs⟩ := hs
  obtain ⟨hb⟩ := hb
  exact ⟨disjunctionElimination hold (Derivation.implicationIntroduction hs) (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.InductionStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.InductionStepProof
