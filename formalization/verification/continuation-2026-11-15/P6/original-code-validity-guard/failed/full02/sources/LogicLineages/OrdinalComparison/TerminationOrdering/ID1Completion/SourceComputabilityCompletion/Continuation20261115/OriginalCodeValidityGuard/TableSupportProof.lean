module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.TableSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalRawListRecursionSupportProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open InternalOriginalOrderSyntaxProof
open OriginalCodeDecoderTable
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroSeed (n : Nat) (bound output : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph2 (tableProgram n) output z bound))) :
    Nonempty (Derivation body Delta (graph1 seed output bound)) := by
  apply InternalAcceptanceSupportProof.programCases seed (Fin.cons bound Fin.elim0) _
  intro beta j Theta seedOut hj hs
  rw [graph1Rename]
  simp only [consTermRename,emptyRename] at hs
  have ho' := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
  simp only [graph2Rename,zRelabel] at ho'
  have hz := recursionZeroValue seed (tableStep n) seedOut (Fin.cons (bound.relabel j) Fin.elim0) hs
  have he := valueUnique (tableProgram n) seedOut (output.relabel j)
    (Fin.cons z (Fin.cons (bound.relabel j) Fin.elim0)) hz ho'
  exact outputTransport seed seedOut (output.relabel j) (Fin.cons (bound.relabel j) Fin.elim0) he hs

theorem nextRowRecover (n : Nat) (fuel bound previous next : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 (tableProgram n) previous fuel bound)))
    (hn : Nonempty (Derivation body Delta (graph2 (tableProgram n) next (suc fuel) bound))) :
    Nonempty (Derivation body Delta (graph2 (nextRow n) next bound previous)) := by
  have ht := recursionRecover seed (tableStep n) next previous fuel (Fin.cons bound Fin.elim0) hp hn
  let xs : Fin 3 → OTerm alpha := Fin.cons fuel (Fin.cons previous (Fin.cons bound Fin.elim0))
  exact binaryRecover (nextRow n) (.projection 2) (.projection 1) next bound previous xs ht
    (projectionValue 2 xs) (projectionValue 1 xs)

theorem rowLookupIntro (n : Nat) (bound previous next index value : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (nextRow n) next bound previous)))
    (hb : Nonempty (Derivation body Delta (Below index (suc bound))))
    (hs : Nonempty (Derivation body Delta (graph2 (OriginalCodeDecoderStep.step n) value previous index))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value index next)) := by
  apply InternalAcceptanceSupportProof.programCases InternalRawListRecursion.lookup
    (Fin.cons index (Fin.cons next Fin.elim0)) _
  intro beta j Theta actual hj hl
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hl
  have hr' := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  rw [graph2Rename] at hr'
  have hb' := InternalGraphCompositionFunctionalityProof.renameInto hb j Theta hj
  simp only [Below,orderRename,sucRelabel] at hb'
  have hs' := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  rw [graph2Rename] at hs'
  have ha := OriginalCodeDecoderTable.Proof.internalRowLookup n body beta Theta
    (bound.relabel j) (previous.relabel j) (next.relabel j) (index.relabel j) actual hr' hb' hl
  have he := valueUnique (OriginalCodeDecoderStep.step n) actual (value.relabel j)
    (Fin.cons (previous.relabel j) (Fin.cons (index.relabel j) Fin.elim0)) ha hs'
  exact outputTransport InternalRawListRecursion.lookup actual (value.relabel j)
    (Fin.cons (index.relabel j) (Fin.cons (next.relabel j) Fin.elim0)) he hl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.TableSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.TableSupportProof
