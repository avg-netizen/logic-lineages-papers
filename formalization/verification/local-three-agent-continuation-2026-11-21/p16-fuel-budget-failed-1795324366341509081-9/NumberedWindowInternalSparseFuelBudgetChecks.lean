module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFuelBudgetTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFuelBudgetInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundExhaustionChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFuelBudgetChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalApplicationCertificateConstructors (graph2)
open ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof (graph2Rename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
open PrimaryMonotonicity.InclusionProof (includedRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseDirectedRounds (poolLength)
open NumberedWindowInternalSparseRoundWindowMotiveProof (roundRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFuelBudgetTargets
open NumberedWindowInternalSparseFuelBudgetSyntaxProof (applyAt)
open NumberedWindowInternalSparseFuelBudgetCoreProof (withCount)
open NumberedWindowInternalSparseFuelBudgetInductionProof (allCounts)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open NumberedWindowInternalSparseRoundExhaustionChecks (exact_ExhaustedBudget)
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_FuelBudget : ExactFuelBudget := by
  intro pred strict E body α Γ i vertices ctx ty seed size a b count
  let A := inputs E i vertices ctx ty seed size a b count
  let Δ := A :: Γ
  obtain ⟨bound⟩ := applyAt E i vertices ctx ty seed size a b count (allCounts pred strict E i)
    ⟨Derivation.hypothesis (body := body) (Gamma := Δ) List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction bound⟩

private theorem withBeforeCount (pred : ExactRetainedPredecessor) (strict : PrimaryUncoveredCount.Targets.InternalStrictDecrease)
    (E : Program 4) (vertices ctx ty seed size a b ac : OTerm α)
    (data : Nonempty (Derivation body Γ (unary poolLength size vertices ⊓ runsAt E size vertices ctx ty seed a b)))
    (current : Nonempty (Derivation body Γ (graph2 PrimaryUncoveredCount.count ac vertices a))) :
    Nonempty (Derivation body Γ (PrimaryMonotonicity.included b a)) := by
  apply withCount vertices b _
  intro β j Δ bc keep next
  rw [includedRename]
  have dat := renameInto data j Δ keep
  simp only [runsAt,conjunctionRename,unaryRename,roundRename,sucRelabel] at dat
  have cc := renameInto current j Δ keep
  rw [graph2Rename] at cc
  obtain ⟨dat⟩ := dat
  obtain ⟨cc⟩ := cc
  obtain ⟨bcGraph⟩ := next
  have runs := Derivation.conjunctionRight dat
  obtain ⟨budget⟩ := applyAt E (size.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j)
    (seed.relabel j) (size.relabel j) (a.relabel j) (b.relabel j) (ac.relabel j)
    (allCounts pred strict E (size.relabel j))
    ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft dat) cc) runs⟩
  obtain ⟨finish⟩ := exact_ExhaustedBudget strict E body β Δ (vertices.relabel j) (ctx.relabel j)
    (ty.relabel j) (seed.relabel j) (size.relabel j) (a.relabel j) (b.relabel j) (ac.relabel j) bc
  exact ⟨Derivation.implicationElimination finish (Derivation.conjunctionIntroduction
    (Derivation.conjunctionIntroduction runs (Derivation.conjunctionIntroduction cc bcGraph)) budget)⟩

theorem exact_LengthStability : ExactLengthStability := by
  intro pred strict E body α Γ vertices ctx ty seed size a b
  let A := unary poolLength size vertices ⊓ runsAt E size vertices ctx ty seed a b
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have stable : Nonempty (Derivation body Δ (PrimaryMonotonicity.included b a)) := by
    apply withCount vertices a _
    intro β j Θ ac keep count
    rw [includedRename]
    have d := renameInto ⟨h⟩ j Θ keep
    simp only [A,runsAt,conjunctionRename,unaryRename,roundRename,sucRelabel] at d
    exact withBeforeCount pred strict E (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
      (size.relabel j) (a.relabel j) (b.relabel j) ac d count
  obtain ⟨stable⟩ := stable
  exact ⟨Derivation.implicationIntroduction stable⟩

#print axioms exact_FuelBudget
#print axioms exact_LengthStability
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFuelBudgetChecks
