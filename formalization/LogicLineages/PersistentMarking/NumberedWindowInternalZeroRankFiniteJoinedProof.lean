module
public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPrefixRenameProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankLeftTapePositionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankExactFuelSpliceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankFiniteJoinedProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalListCodecDecompositionSupportProof (nonzeroRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph5Rename)
open NumberedWindowInternalParameterizedPositiveFold (zeroPositive)
open NumberedWindowInternalZeroRankOpenPathBuildProof (OriginalZeroPrefix)
open NumberedWindowInternalZeroRankPrefixRenameProof
open NumberedWindowInternalZeroRankLeftTapePositionProof (Rows tape fuelAfter position)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The actual finite left certificate tape is constructed from the
physical cons rows. At its genuine suffix cursor the real equality
aligns the two current states, and the actual zero suffix is replayed.
The combined arithmetic fuel gap and nonemptiness are held exact
object reports. No arbitrary symbolic append is assumed. -/
theorem exact_OpenJoinedFiniteZeroCertificate (g : Program 1) (raw : Program 5) (L : Program 3)
    (ctx ty source suffix a b rightFuel rightState dst extra : OTerm α)
    (hops : List (OTerm α))
    (left : Rows B Γ g raw L ctx ty (suc source) hops (suc a))
    (middle : Nonempty (Derivation B Γ (eqn a b)))
    (right : OriginalZeroPrefix B Γ g raw L ctx ty (suc b) suffix rightFuel rightState z (suc dst)) :
    let joined := tape id hops suffix
    let used := fuelAfter hops (z : OTerm α)
    Nonempty (Derivation B Γ (eqn (add (add used rightFuel) extra) joined)) →
    Nonempty (Derivation B Γ (eqn joined z).not) →
    Nonempty (Derivation B Γ (programGraph (zeroPositive g raw L) (suc z) ![ctx,ty,source,joined,dst])) := by
  intro joined used gap nz
  apply position left suffix (programGraph (zeroPositive g raw L) (suc z) ![ctx,ty,source,joined,dst])
  intro β j Δ state keep loop scratch
  rw [graph5Rename,sucRelabel,zRelabel]
  rw [sucRelabel] at loop scratch
  have eq := renameInto middle j Δ keep
  rw [eqnRelabel] at eq
  have fuel := renameInto gap j Δ keep
  rw [eqnRelabel,addRelabel,addRelabel] at fuel
  have ne := renameInto nz j Δ keep
  rw [nonzeroRename] at ne
  have good := exact_OriginalZeroPrefixRename j keep g raw L ctx ty (suc b) suffix rightFuel rightState z (suc dst) right
  rw [sucRelabel,zRelabel,sucRelabel] at good
  exact NumberedWindowInternalZeroRankExactFuelSpliceProof.positive g raw L
    (ctx.relabel j) (ty.relabel j) (source.relabel j) (joined.relabel j) (used.relabel j) state
    (suffix.relabel j) (a.relabel j) (b.relabel j) (rightFuel.relabel j) (rightState.relabel j)
    (dst.relabel j) (extra.relabel j) loop scratch eq good fuel ne

#print axioms exact_OpenJoinedFiniteZeroCertificate
end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankFiniteJoinedProof
