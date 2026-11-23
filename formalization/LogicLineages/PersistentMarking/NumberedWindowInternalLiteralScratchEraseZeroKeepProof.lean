module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseBranchFlagsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchQueryCasesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseZeroKeepProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalAcceptanceSupportProof (programCases)
open InternalControlGraphSupportProof (equalEqn)
open InternalGraphCompositionEqualityProof (graphInputTransport)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel)
open InternalTagArithmeticSupportProof (refl)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open NumberedWindowInternalScratchQueryCasesProof (notRename)
open NumberedWindowInternalLiteralScratchErase (state)
open NumberedWindowInternalLiteralScratchEraseCoordinatesProof (coordinates)
open NumberedWindowInternalLiteralScratchEraseKeepProof (cons absent)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

private theorem pairRestTransport (acc bit oldRest newRest : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn oldRest newRest)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit oldRest))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit newRest)) := by
  unfold graph2 programGraph at hp ⊢
  apply graphInputTransport body alpha 2 Delta (OrdinaryArithmetic.graphFormula InternalPairing.pairing)
    acc ![bit,oldRest] ![bit,newRest] _ hp
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · change Nonempty (Derivation body Delta (equal bit bit))
    rw [equalEqn]
    exact ⟨refl bit⟩
  · obtain rfl := Fin.eq_zero k
    change Nonempty (Derivation body Delta (equal oldRest newRest))
    rw [equalEqn]
    exact he

/-- If the actual zero-flag tail has not changed and the head misses, the
entire actual cons cell is the retained residual. Open its canonical pair
in object logic; no arithmetic witness or tape equality oracle is supplied. -/
theorem keepSame (raw head tail needle acc rest actual bit remaining : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc z rest)))
    (hr : Nonempty (Derivation body Delta (eqn rest tail)))
    (hn : Nonempty (Derivation body Delta (eqn head needle).not))
    (ha : Nonempty (Derivation body Delta (graph2 state actual raw needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing actual bit remaining))) :
    Nonempty (Derivation body Delta (eqn bit z ⊓ eqn remaining raw)) := by
  apply programCases InternalPairing.pairing ![z,raw] _
  intro beta j Theta out hj ho
  have hx : (fun i => (![z,raw] i).relabel j) = ![z,raw.relabel j] := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · change (z : OTerm alpha).relabel j = z
      exact zRelabel j
    · exact Fin.cases rfl (fun t => Fin.elim0 t) k
  rw [hx] at ho
  have hcj := renameInto hc j Theta hj
  have htj := renameInto ht j Theta hj
  have hpj := renameInto hp j Theta hj
  have hrj := renameInto hr j Theta hj
  have hnj := renameInto hn j Theta hj
  have haj := renameInto ha j Theta hj
  have hapj := renameInto hap j Theta hj
  simp only [graph2Rename,zRelabel] at hcj htj hpj haj hapj
  rw [eqnRelabel] at hrj
  simp only [notRename,eqnRelabel] at hnj
  simp only [conjunctionRename,eqnRelabel,zRelabel]
  have pairTail := pairRestTransport (acc.relabel j) z (rest.relabel j) (tail.relabel j) hrj hpj
  have row := absent (head.relabel j) (acc.relabel j) (needle.relabel j)
    (tail.relabel j) (raw.relabel j) out pairTail hcj ho hnj
  have hcValue := cons (raw.relabel j) (head.relabel j) (tail.relabel j) (needle.relabel j)
    (acc.relabel j) out hcj htj row
  exact coordinates (raw.relabel j) (needle.relabel j) (actual.relabel j) (bit.relabel j)
    (remaining.relabel j) out z (raw.relabel j) haj hapj hcValue ho

#print axioms keepSame
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseZeroKeepProof
