module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFuelBudgetSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundChargeChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFuelBudgetCoreProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationCertificateConstructors (graph2)
open ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof (graph2Rename)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc sucRelabel)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseRoundWindowMotiveProof (roundRename)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseDirectedRounds (rounds roundsTape)
open NumberedWindowInternalSparseRoundChargeChecks (exact_RoundCharge)
open NumberedWindowInternalSparseFuelBudgetSyntaxProof
open NumberedWindowInternalSparseFuelBudgetTargets
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem inputsRename (E : Program 4) (i vertices ctx ty seed size a b count : OTerm α)
    {β : Type} (j : α → β) :
    (inputs E i vertices ctx ty seed size a b count).relabel j = inputs E (i.relabel j)
      (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) (size.relabel j)
      (a.relabel j) (b.relabel j) (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (inputs E i vertices ctx ty seed size a b count).subst (fun a => emb (.var (j a))) = _
  rw [inputsSubst]
  simp only [← termRelabelAsSubst]

theorem withCount (vertices out : OTerm α) (goal : Formula α)
    (each : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (count : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (graph2 PrimaryUncoveredCount.count count (vertices.relabel j) (out.relabel j))) →
      Nonempty (Derivation body Δ (goal.relabel j))) : Nonempty (Derivation body Γ goal) := by
  apply programCases PrimaryUncoveredCount.count (Fin.cons vertices (Fin.cons out Fin.elim0)) _
  intro β j Δ count keep h
  apply each β j Δ count keep
  simpa only [ID1Completion.InternalRecursionGraphStepSyntaxProof.consTermRename,
    ID1Completion.InternalControlGraphSupportProof.emptyRename] using h

private theorem withPrevious (pred : ExactRetainedPredecessor) (strict : PrimaryUncoveredCount.Targets.InternalStrictDecrease)
    (E : Program 4) (i vertices ctx ty seed size a b count previous : OTerm α)
    (row : Nonempty (Derivation body Γ (AtCount E i)))
    (data : Nonempty (Derivation body Γ (inputs E (suc i) vertices ctx ty seed size a b count)))
    (prior : Nonempty (Derivation body Γ (roundGraph E previous i vertices ctx ty seed))) :
    Nonempty (Derivation body Γ (PrimaryFiniteDescent.budget (suc i) size count a b)) := by
  apply withCount vertices previous _
  intro β j Δ oldCount keep old
  rw [budgetRename,sucRelabel]
  have pr := renameInto prior j Δ keep
  rw [roundRename] at pr
  have dat := renameInto data j Δ keep
  rw [inputsRename,sucRelabel] at dat
  have rr := renameInto row j Δ keep
  rw [atCountRename] at rr
  obtain ⟨pr⟩ := pr
  obtain ⟨dat⟩ := dat
  obtain ⟨old⟩ := old
  have gc := Derivation.conjunctionLeft dat
  have ab := Derivation.conjunctionRight dat
  have pa := Derivation.conjunctionIntroduction pr (Derivation.conjunctionLeft ab)
  obtain ⟨budget⟩ := applyAt E (i.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j)
    (seed.relabel j) (size.relabel j) (previous.relabel j) (a.relabel j) oldCount rr
    ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft gc) old) pa⟩
  obtain ⟨charge⟩ := exact_RoundCharge pred strict E body β Δ (vertices.relabel j) (ctx.relabel j)
    (ty.relabel j) (seed.relabel j) (i.relabel j) (previous.relabel j) (a.relabel j) (b.relabel j)
    (size.relabel j) oldCount (count.relabel j)
  have step := Derivation.conjunctionIntroduction pa (Derivation.conjunctionIntroduction old (Derivation.conjunctionRight gc))
  exact ⟨Derivation.implicationElimination charge (Derivation.conjunctionIntroduction
    (Derivation.conjunctionIntroduction step (Derivation.conjunctionRight ab)) budget)⟩

theorem successorCore (pred : ExactRetainedPredecessor) (strict : PrimaryUncoveredCount.Targets.InternalStrictDecrease)
    (E : Program 4) (i vertices ctx ty seed size a b count : OTerm α)
    (row : Nonempty (Derivation body Γ (AtCount E i)))
    (data : Nonempty (Derivation body Γ (inputs E (suc i) vertices ctx ty seed size a b count))) :
    Nonempty (Derivation body Γ (PrimaryFiniteDescent.budget (suc i) size count a b)) := by
  apply programCases (rounds E) (roundsTape i vertices ctx ty seed) _
  intro β j Δ prev keep graph
  rw [budgetRename,sucRelabel]
  have rr := renameInto row j Δ keep
  rw [atCountRename] at rr
  have d := renameInto data j Δ keep
  rw [inputsRename,sucRelabel] at d
  have tape : (fun k => (roundsTape i vertices ctx ty seed k).relabel j) =
      roundsTape (i.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) := by
    funext k
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c =>
      Fin.cases ?_ (fun d => Fin.cases ?_ (fun e => Fin.elim0 e) d) c) b) a) k <;> rfl
  rw [tape] at graph
  exact withPrevious pred strict E _ _ _ _ _ _ _ _ _ prev rr d graph

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFuelBudgetCoreProof
