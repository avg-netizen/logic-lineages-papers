module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeMemberTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanMemberProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeMember
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalControlGraphSupportProof (equalEqn valueUnique)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectSharedTapeMemberTargets
open NumberedWindowInternalDirectInsertedRowCases (exactOpenInsertedRowCases)
open NumberedWindowInternalDirectInsertedScanMember (exactOpenScanMember)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser)
open NumberedWindowInternalDirectInsertedRowTargets (oneTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem samePool (raw decoded common dom : OTerm α)
    (old : Nonempty (Derivation B Γ (unary parser (suc decoded) raw)))
    (canonical : Nonempty (Derivation B Γ (unary parser (suc common) raw)))
    (member : Nonempty (Derivation B Γ (programGraph scratchMember oneTerm ![decoded,dom]))) :
    Nonempty (Derivation B Γ (programGraph scratchMember oneTerm ![common,dom])) := by
  obtain ⟨e⟩ := valueUnique parser (suc decoded) (suc common) ![raw] old canonical
  unfold programGraph at member ⊢
  apply graphInputTransport B α 2 Γ (OrdinaryArithmetic.graphFormula scratchMember)
    oneTerm ![decoded,dom] ![common,dom] _ member
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change Nonempty (Derivation B Γ (equal decoded common))
    rw [equalEqn]
    exact ⟨cancelSuc e⟩
  · obtain rfl := Fin.eq_zero j
    change Nonempty (Derivation B Γ (equal dom dom))
    rw [equalEqn]
    exact ⟨ID1Completion.InternalTagArithmeticSupportProof.refl dom⟩

private theorem pinRow (r : Program 3) (raw row decoded common target dom cert : OTerm α)
    (ps : Nonempty (Derivation B Γ (unary parser (suc common) raw)))
    (reports : NumberedWindowInternalDirectInsertedRowCasesTargets.Reports r B Γ raw row decoded target dom cert) :
    NumberedWindowInternalDirectInsertedRowCasesTargets.Reports r B Γ raw row common target dom cert := by
  refine ⟨ps,reports.targetField,reports.dominatorField,reports.certificateField,?_⟩
  obtain ⟨h⟩ := reports.original
  have rest := Derivation.conjunctionRight h
  obtain ⟨m⟩ := samePool raw decoded common dom reports.parsed ps ⟨Derivation.conjunctionLeft rest⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft h)
    (Derivation.conjunctionIntroduction m (Derivation.conjunctionRight rest))⟩

theorem exactOpenSharedTapeMember : ExactOpenSharedTapeMember := by
  intro srcObs dstObs r B α Γ src dst kept removed inserted s t k d a p sk tp row goal shared mem next
  obtain ⟨law⟩ := exactOpenScanMember r B α Γ a removed row
  obtain ⟨inside⟩ := mem
  obtain ⟨accepted⟩ := shared.scanObserved
  have checked := Derivation.implicationElimination law
    (Derivation.conjunctionIntroduction accepted inside)
  apply exactOpenInsertedRowCases r B α Γ removed row goal ⟨checked⟩
  intro β j Δ decoded target dom cert keep selected
  have parsed := renameParser removed d shared.removedParsed j Δ keep
  exact next β j Δ target dom cert keep
    (pinRow r (removed.relabel j) (row.relabel j) decoded (d.relabel j) target dom cert parsed selected)

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeMember
