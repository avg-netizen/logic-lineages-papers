module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseExchangeTransportTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseExchangeTransportDomainProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSymmetricExchangeChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumEdgePoolProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseExchangeTransportChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSupportProof (congSuc symm)
open NumberedWindowInternalSparseSymmetricExchangeTargets (pairedExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalSparseCoverOccurrenceTargets (occursInCover)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseMinimumEdgePoolProof (acceptedEdgeRename)
open NumberedWindowInternalSparseExchangeTransportTargets

theorem exact_PairedEdgeTransport : ExactPairedEdgeTransport := by
  intro C s baseX W body α Γ ctx ty a b x
  let X := guardedExchange C s (pairedExchange baseX)
  let source := leastGraph C X W s ctx ty a x
  let edge := acceptEdge (edge4 X W) ctx ty a b
  let Δ := (source ⊓ (edge ⊓ occursInCover C s b b)) :: Γ
  have d : Derivation body Δ (source ⊓ (edge ⊓ occursInCover C s b b)) := Derivation.hypothesis List.mem_cons_self
  have lhs := Derivation.conjunctionLeft d
  let e := Derivation.conjunctionLeft (Derivation.conjunctionRight d)
  have existsRight := NumberedWindowInternalSparseExchangeTransportDomainProof.targetExists
    C X W s ctx ty a b x ⟨lhs⟩ ⟨Derivation.conjunctionRight (Derivation.conjunctionRight d)⟩
  have conclusion : Nonempty (Derivation body Δ (leastGraph C X W s ctx ty b x)) := by
    apply NumberedWindowInternalSparsePackedDomainSyntaxProof.casesLeast C X W s ctx ty b _ existsRight
    intro β j Θ y keep right
    rw [leastRename]
    have l := renameInto ⟨lhs⟩ j Θ keep
    change Nonempty (Derivation body Θ ((leastGraph C X W s ctx ty a x).relabel j)) at l
    rw [leastRename] at l
    have arc := renameInto ⟨e⟩ j Θ keep
    change Nonempty (Derivation body Θ ((acceptEdge (edge4 X W) ctx ty a b).relabel j)) at arc
    rw [acceptedEdgeRename] at arc
    obtain ⟨r⟩ := NumberedWindowInternalSparseSymmetricExchangeChecks.exact_PairedEdgeMinimumEquality C s baseX W
      body β Θ (ctx.relabel j) (ty.relabel j) (a.relabel j) (b.relabel j) (x.relabel j) y
    obtain ⟨l⟩ := l
    obtain ⟨arc⟩ := arc
    obtain ⟨right⟩ := right
    have same := Derivation.implicationElimination r
      (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction l right) arc)
    exact outputTransport (packedLeastProgram C X W s) (suc y) (suc (x.relabel j))
      ![ctx.relabel j,ty.relabel j,b.relabel j] ⟨congSuc (symm same)⟩ ⟨right⟩
  obtain ⟨conclusion⟩ := conclusion
  exact ⟨Derivation.implicationIntroduction conclusion⟩
#print axioms exact_PairedEdgeTransport
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseExchangeTransportChecks
