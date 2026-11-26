module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinPairedPackedLeastProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredWindowOpenReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinPairedLeastFromCoveredWindowProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (congSuc symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge edgeTape)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (pairedExchange)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (coveredWindow)
open NumberedWindowInternalSparseCoveredWindowOpenReportProof (exact_CoveredWindowReport)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (casesLeast)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalThinRoundExhaustionTargets (CountLengthBound)
open NumberedWindowInternalThinUncoveredCountTargets (InternalStrictDecrease)
open NumberedWindowInternalThinPairedPackedLeastProof

private theorem edgeRename {α β : Type} (E : Program 4) (ctx ty a b : OTerm α) (j : α → β) :
    (acceptEdge E ctx ty a b).relabel j = acceptEdge E (ctx.relabel j) (ty.relabel j) (a.relabel j) (b.relabel j) := by
  simp only [acceptEdge,programRename,edgeTape,quadInputsRename,sucRelabel,zRelabel]

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- An actual covered target window supplies its original successful
least. The genuine paired guarded edge makes that target's actual least
equal the held successful least on the source. The target's least
call is not an input. -/
theorem exact_OpenThinPairedLeastFromCoveredWindow (bound : CountLengthBound) (strict : InternalStrictDecrease)
    (C : Program 3) (base : Program 2) (baseW : Program 3) (s : Settings)
    (ctx ty a b x : OTerm α) :
    let X := guardedExchange C s (pairedExchange base)
    let W := coveredWindow C s baseW
    Nonempty (Derivation B Γ (leastGraph C X W s ctx ty a x)) →
    Nonempty (Derivation B Γ (acceptEdge (edge4 X W) ctx ty a b)) →
    Nonempty (Derivation B Γ (windowAt W ctx ty b)) →
    Nonempty (Derivation B Γ (leastGraph C X W s ctx ty b x)) := by
  intro X W old edge window
  obtain ⟨own⟩ := exact_CoveredWindowReport C X s baseW B α Γ ctx ty b
  obtain ⟨provided⟩ := window
  have bits := Derivation.implicationElimination own provided
  apply casesLeast C X W s ctx ty b _ ⟨Derivation.conjunctionRight (Derivation.conjunctionRight bits)⟩
  intro β j Δ selected keep found
  rw [leastRename]
  have old' := renameInto old j Δ keep
  rw [leastRename] at old'
  have edge' := renameInto edge j Δ keep
  rw [edgeRename] at edge'
  obtain ⟨same⟩ := exact_OpenThinPairedPackedLeast bound strict C base W s
    (ctx.relabel j) (ty.relabel j) (a.relabel j) (b.relabel j) (x.relabel j) selected old' found edge'
  exact outputTransport (packedLeastProgram C X W s) (suc selected) (suc (x.relabel j))
    ![ctx.relabel j,ty.relabel j,b.relabel j] ⟨congSuc (symm same)⟩ found

#print axioms exact_OpenThinPairedLeastFromCoveredWindow
end LogicLineages.PersistentMarking.NumberedWindowInternalThinPairedLeastFromCoveredWindowProof
