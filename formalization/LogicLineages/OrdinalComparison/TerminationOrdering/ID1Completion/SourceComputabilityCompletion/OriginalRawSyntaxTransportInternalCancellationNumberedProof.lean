module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationNumberedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalCancellation
open OriginalRawSyntaxTransportInternalCancellationBindingProof OriginalRawSyntaxTransportInternalCancellationSyntaxProof
open OriginalRawSyntaxTransportInternalParametersQueryProof
open OriginalRawSyntaxTransportInternalFoldNumberedProof OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorBoundsProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem numberedRightInverseAt (raw shifted d k label head tau base types extras baseOut extrasOut : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .shift) (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,tau,base,types,extras])))
    (hbase : Nonempty (Derivation body Delta (graph3 (fold .shift) baseOut (numeral 0) k base)))
    (hextras : Nonempty (Derivation body Delta (graph3 (fold .shift) extrasOut (numeral 0) k extras)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold .shift) shifted (numeral 0) k raw))) :
    Nonempty (Derivation body Delta (graph3 (fold .erase) raw d k shifted)) := by
  have hf := numberedFields raw label head tau base types extras hc
  have hl := binaryChildrenStrict raw base extras (andLeft hf) (andLeft (andRight hf)) (andRight (andRight hf))
  have heBase := belowRawApply (fold .shift) (fold .erase) raw base d k baseOut hi (andLeft hl) hbase
  have heExtras := belowRawApply (fold .shift) (fold .erase) raw extras d k extrasOut hi (andRight hl) hextras
  have hshift := numberedForward .shift raw shifted (numeral 0) k label head tau base types extras baseOut extrasOut
    hc hbase hextras hs
  exact numberedBackward .erase shifted raw d k label head tau baseOut types extrasOut base extras
    hshift heBase heExtras hc

/-- Normalize the six input vector before specializing its concrete Program. -/
theorem tupleSixRename {beta : Type} (a b c d e f : OTerm alpha) (j : alpha → beta) :
    (fun i => (![a,b,c,d,e,f] i).relabel j) =
      ![a.relabel j,b.relabel j,c.relabel j,d.relabel j,e.relabel j,f.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)))))) i

theorem numberedRightInverse (raw shifted d k label head tau base types extras : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .shift) (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,tau,base,types,extras])))
    (hs : Nonempty (Derivation body Delta (graph3 (fold .shift) shifted (numeral 0) k raw))) :
    Nonempty (Derivation body Delta (graph3 (fold .erase) raw d k shifted)) := by
  apply binaryChildCases (fold .shift) (numeral 0) k base extras _
  intro beta j Theta baseOut extrasOut hj hbase hextras
  rw [graph3Rename]
  have hi' := renameInto hi j Theta hj
  have hc' := renameInto hc j Theta hj
  have hs' := renameInto hs j Theta hj
  rw [belowRawRename] at hi'
  simp only [programRename,tupleSixRename] at hc'
  simp only [graph3Rename,numeral,zRelabel] at hs'
  simp only [numeral,zRelabel] at hbase hextras
  exact numberedRightInverseAt (raw.relabel j) (shifted.relabel j) (d.relabel j) (k.relabel j)
    (label.relabel j) (head.relabel j) (tau.relabel j) (base.relabel j) (types.relabel j) (extras.relabel j)
    baseOut extrasOut hi' hc' hbase hextras hs'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationNumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationNumberedProof
