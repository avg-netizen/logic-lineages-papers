module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFixedArgumentAdjacentProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparsePositiveTransitivityTargets (supplied)
open NumberedWindowInternalSparsePositiveTransitivityTransportProof (moveSource)
open NumberedWindowInternalSparsePositiveTransitivityChecks (exact_OpenPositiveTransitivity)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Same actual context/type, same fixed raw argument, and the literally
same joining raw function. Only then do the two original least calls
necessarily name the same application class. No quotient congruence. -/
theorem identicalMid (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx dom cod arg join a b : OTerm α)
    (first : Nonempty (Derivation body Γ
      (leastGraph C X W s ctx cod (auxiliaryTerm dom cod join arg) a)))
    (second : Nonempty (Derivation body Γ
      (leastGraph C X W s ctx cod (auxiliaryTerm dom cod join arg) b))) :
    Nonempty (Derivation body Γ (eqn a b)) := by
  obtain ⟨e⟩ := valueUnique (packedLeastProgram C X W s) (suc a) (suc b)
    ![ctx,cod,auxiliaryTerm dom cod join arg] first second
  exact ⟨cancelSuc e⟩

/-- Join two actual mapped positive rows meeting at the same raw function.
The actual map reports need not have used the same eigenvariable for its
class; graph functionality and positive witness composition pay that gap. -/
theorem composeAdjacent (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (raw : Program 5) (ctx dom cod arg join source first a b second target : OTerm α) :
    let least := packedLeastProgram C X W s
    Nonempty (Derivation body Γ (leastGraph C X W s ctx cod (auxiliaryTerm dom cod join arg) a)) →
    Nonempty (Derivation body Γ (leastGraph C X W s ctx cod (auxiliaryTerm dom cod join arg) b)) →
    Nonempty (Derivation body Γ (positiveAt raw least ctx cod source first a)) →
    Nonempty (Derivation body Γ (positiveAt raw least ctx cod b second target)) →
    Nonempty (Derivation body Γ (supplied raw least ctx cod source target)) := by
  intro least aReport bReport hfirst hsecond
  have e := identicalMid C X W s ctx dom cod arg join b a bReport aReport
  obtain ⟨next⟩ := moveSource raw least ctx cod b a second target e hsecond
  obtain ⟨prior⟩ := hfirst
  exact closedApply (exact_OpenPositiveTransitivity body raw least α ctx cod source first a second target)
    ⟨Derivation.conjunctionIntroduction prior next⟩

#print axioms identicalMid
#print axioms composeAdjacent
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFixedArgumentAdjacentProof
