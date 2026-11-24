module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseCoordinatesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseConstructQueriesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseBranchFlagsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalAcceptanceSupportProof (programCases)
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel sucRelabel zRelabel)
open SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open NumberedWindowInternalLiteralScratchErase (state)
open NumberedWindowInternalLiteralScratchEraseCoordinatesProof (coordinates chosenHeadCoordinates)
open NumberedWindowInternalLiteralScratchEraseKeepProof (cons alreadyFound absent)
open NumberedWindowInternalLiteralScratchEraseConstructQueriesProof (queries recover)

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

/-- Real hit branch, with the exact result pair obtained by object program
totality instead of an externally supplied arithmetic witness. -/
theorem headHit (list head tail needle acc rest actual bit remaining : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc z rest)))
    (he : Nonempty (Derivation body Delta (eqn head needle)))
    (ha : Nonempty (Derivation body Delta (graph2 state actual list needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing actual bit remaining))) :
    Nonempty (Derivation body Delta (eqn bit (suc z))) := by
  apply programCases InternalPairing.pairing ![suc z,rest] _
  intro beta j Theta out hj ho
  have hx : (fun i => (![suc z,rest] i).relabel j) = ![suc z,rest.relabel j] := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · change (suc (z : OTerm alpha)).relabel j = suc z
      simp only [sucRelabel,zRelabel]
    · exact Fin.cases rfl (fun t => Fin.elim0 t) k
  rw [hx] at ho
  have hcj := renameInto hc j Theta hj
  have htj := renameInto ht j Theta hj
  have hpj := renameInto hp j Theta hj
  have hej := renameInto he j Theta hj
  have haj := renameInto ha j Theta hj
  have hapj := renameInto hap j Theta hj
  simp only [graph2Rename,zRelabel] at hcj htj hpj haj hapj
  rw [eqnRelabel] at hej
  simp only [eqnRelabel,sucRelabel,zRelabel]
  obtain ⟨d⟩ := chosenHeadCoordinates (list.relabel j) (head.relabel j) (tail.relabel j)
    (needle.relabel j) (acc.relabel j) (rest.relabel j) out (actual.relabel j)
    (bit.relabel j) (remaining.relabel j) hcj htj hpj hej ho haj hapj
  exact ⟨Derivation.conjunctionLeft d⟩

/-- If a real tail deletion already found the occurrence, the exact rebuilt
cons preserves success. Both rebuilt constructor witnesses are opened in object logic. -/
theorem tailHit (list head tail needle acc rest actual bit remaining : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc (suc z) rest)))
    (ha : Nonempty (Derivation body Delta (graph2 state actual list needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing actual bit remaining))) :
    Nonempty (Derivation body Delta (eqn bit (suc z))) := by
  apply queryCases queries ![suc z,head,rest] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![suc z,head,rest] i).relabel j) = ![suc z,head.relabel j,rest.relabel j] := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · change (suc (z : OTerm alpha)).relabel j = suc z
      simp only [sucRelabel,zRelabel]
    · exact Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t)) k
  rw [hx] at hq
  obtain ⟨hk,ho⟩ := recover (suc z) (head.relabel j) (rest.relabel j) ys hq
  have hcj := renameInto hc j Theta hj
  have htj := renameInto ht j Theta hj
  have hpj := renameInto hp j Theta hj
  have haj := renameInto ha j Theta hj
  have hapj := renameInto hap j Theta hj
  simp only [graph2Rename,zRelabel,sucRelabel] at hcj htj hpj haj hapj
  simp only [eqnRelabel,sucRelabel,zRelabel]
  have step := alreadyFound (head.relabel j) (acc.relabel j) (needle.relabel j)
    (rest.relabel j) (ys 0) (ys 1) hpj hk ho
  have kept := cons (list.relabel j) (head.relabel j) (tail.relabel j)
    (needle.relabel j) (acc.relabel j) (ys 1) hcj htj step
  obtain ⟨d⟩ := coordinates (list.relabel j) (needle.relabel j) (actual.relabel j)
    (bit.relabel j) (remaining.relabel j) (ys 1) (suc z) (ys 0) haj hapj kept ho
  exact ⟨Derivation.conjunctionLeft d⟩

/-- Both miss: the exact retained-head state keeps the zero flag. -/
theorem bothMiss (list head tail needle acc rest actual bit remaining : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc z rest)))
    (hn : Nonempty (Derivation body Delta (eqn head needle).not))
    (ha : Nonempty (Derivation body Delta (graph2 state actual list needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing actual bit remaining))) :
    Nonempty (Derivation body Delta (eqn bit z)) := by
  apply queryCases queries ![z,head,rest] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![z,head,rest] i).relabel j) = ![z,head.relabel j,rest.relabel j] := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · change (z : OTerm alpha).relabel j = z
      exact zRelabel j
    · exact Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t)) k
  rw [hx] at hq
  obtain ⟨hk,ho⟩ := recover z (head.relabel j) (rest.relabel j) ys hq
  have hcj := renameInto hc j Theta hj
  have htj := renameInto ht j Theta hj
  have hpj := renameInto hp j Theta hj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn head needle).relabel j).not) at hnj
  rw [eqnRelabel] at hnj
  have haj := renameInto ha j Theta hj
  have hapj := renameInto hap j Theta hj
  simp only [graph2Rename,zRelabel,sucRelabel] at hcj htj hpj haj hapj
  simp only [eqnRelabel,sucRelabel,zRelabel]
  have step := absent (head.relabel j) (acc.relabel j) (needle.relabel j)
    (rest.relabel j) (ys 0) (ys 1) hpj hk ho hnj
  have kept := cons (list.relabel j) (head.relabel j) (tail.relabel j)
    (needle.relabel j) (acc.relabel j) (ys 1) hcj htj step
  obtain ⟨d⟩ := coordinates (list.relabel j) (needle.relabel j) (actual.relabel j)
    (bit.relabel j) (remaining.relabel j) (ys 1) z (ys 0) haj hapj kept ho
  exact ⟨Derivation.conjunctionLeft d⟩

#print axioms headHit
#print axioms tailHit
#print axioms bothMiss
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseBranchFlagsProof
