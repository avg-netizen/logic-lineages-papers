module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphZeroEliminationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsRecursionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof
  (programRename recursionZeroValue outputTransport valueUnique)
open ID1Completion.InternalRecursionGraphSuccessorIntroductionProof (recursionSuccessorIntroduction)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (consTermRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveOutputTargets (equivalent)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)} {n : Nat}

theorem zeroRead (f : Program n) (g : Program (n+2)) (out : OTerm α) (xs : Fin n → OTerm α)
    (actual : Nonempty (Derivation body Γ (programGraph (.recursion f g) out (Fin.cons z xs)))) :
    Nonempty (Derivation body Γ (programGraph f out xs)) :=
  ID1Completion.InternalRecursionClosureLogicProof.closedApply
    (ID1Completion.InternalRecursionGraphZeroEliminationProof.actualOriginalRecursionZeroElimination
      body n α (OrdinaryArithmetic.graphFormula f) (OrdinaryArithmetic.graphFormula g) out xs) actual

theorem succWrite (f : Program n) (g : Program (n+2)) (out fuel prior : OTerm α)
    (xs : Fin n → OTerm α)
    (before : Nonempty (Derivation body Γ (programGraph (.recursion f g) prior (Fin.cons fuel xs))))
    (step : Nonempty (Derivation body Γ (programGraph g out (Fin.cons fuel (Fin.cons prior xs))))) :
    Nonempty (Derivation body Γ (programGraph (.recursion f g) out (Fin.cons (suc fuel) xs))) :=
  recursionSuccessorIntroduction Γ (OrdinaryArithmetic.graphFormula f) (OrdinaryArithmetic.graphFormula g)
    out fuel prior xs before step

theorem succRead (f : Program n) (g : Program (n+2)) (out fuel prior : OTerm α)
    (xs : Fin n → OTerm α)
    (before : Nonempty (Derivation body Γ (programGraph (.recursion f g) prior (Fin.cons fuel xs))))
    (actual : Nonempty (Derivation body Γ (programGraph (.recursion f g) out (Fin.cons (suc fuel) xs)))) :
    Nonempty (Derivation body Γ (programGraph g out (Fin.cons fuel (Fin.cons prior xs)))) := by
  apply programCases g (Fin.cons fuel (Fin.cons prior xs)) _
  intro β j Δ v keep hv
  simp only [programRename,consTermRename] at hv ⊢
  have earlier := renameInto before j Δ keep
  have later := renameInto actual j Δ keep
  simp only [programRename,consTermRename,sucRelabel] at earlier later
  have proposed := succWrite f g v (fuel.relabel j) (prior.relabel j)
    (fun k => (xs k).relabel j) earlier hv
  exact outputTransport g v (out.relabel j) _ (valueUnique _ _ _ _ proposed later) hv

theorem conditional (known left right : Formula α)
    (forward : ∀ Δ, Nonempty (Derivation body Δ known) → Nonempty (Derivation body Δ left) →
      Nonempty (Derivation body Δ right))
    (backward : ∀ Δ, Nonempty (Derivation body Δ known) → Nonempty (Derivation body Δ right) →
      Nonempty (Derivation body Δ left)) :
    Nonempty (Derivation body Γ (known.imp (equivalent left right))) := by
  obtain ⟨a⟩ := forward (left :: known :: Γ)
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨b⟩ := backward (right :: known :: Γ)
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction a) (Derivation.implicationIntroduction b))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsRecursionProof
