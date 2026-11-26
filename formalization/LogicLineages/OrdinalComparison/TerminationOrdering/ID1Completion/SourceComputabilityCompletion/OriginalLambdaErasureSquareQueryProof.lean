module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareQueryTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- All queries are original total Programs. The raw child erase uses the
actual successor cutoff before any body repacking; the context is untouched. -/
def queries : Fin 10 → Program 7 :=
  let arrow := consOf (.projection 0) (.projection 1)
  let child := pairOf (.projection 1) (.projection 2)
  let inner := pairOf (.projection 0) (.projection 2)
  let raw := pairOf (OriginalRawSyntaxTransport.constant 7 1) inner
  let erased := .composition OriginalRawSyntaxTransport.eraseRaw
    ![.projection 3,.composition .succ (fun _ : Fin 1 => .projection 4),.projection 2]
  let childOut := pairOf (.projection 1) erased
  let innerOut := pairOf (.projection 0) erased
  let rawOut := pairOf (OriginalRawSyntaxTransport.constant 7 1) innerOut
  ![arrow,child,inner,raw,erased,childOut,innerOut,rawOut,
    consOf (.projection 0) (.projection 5),consOf (.projection 0) (.projection 6)]

theorem actualOriginalLambdaErasureSquareQuery :
    OriginalLambdaErasureSquareQueryTargets.ActualOriginalLambdaErasureSquareQuery := by
  intro body alpha Delta s out domain codomain childRaw erasedType cutoff gamma extended psi hp he hc consume
  let xs : Fin 7 → OTerm alpha := ![domain,codomain,childRaw,erasedType,cutoff,gamma,extended]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases queries xs psi
  intro beta j ys Theta hj hq
  let xx : Fin 7 → OTerm beta := fun i => (xs i).relabel j
  have hp' := renameInto hp j Theta hj
  have he' := renameInto he j Theta hj
  rw [graph3Rename] at hp' he'
  have hc' := renameInto hc j Theta hj
  rw [OriginalContextInsertionSyntaxProof.insertRename] at hc'
  have arrow := binaryRecover InternalListCodec.consCode (.projection 0) (.projection 1)
    (ys 0) (domain.relabel j) (codomain.relabel j) xx (hq 0) (projectionValue 0 xx) (projectionValue 1 xx)
  have child := binaryRecover InternalPairing.pairing (.projection 1) (.projection 2)
    (ys 1) (codomain.relabel j) (childRaw.relabel j) xx (hq 1) (projectionValue 1 xx) (projectionValue 2 xx)
  have inner := binaryRecover InternalPairing.pairing (.projection 0) (.projection 2)
    (ys 2) (domain.relabel j) (childRaw.relabel j) xx (hq 2) (projectionValue 0 xx) (projectionValue 2 xx)
  have raw := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 7 1)
    (pairOf (.projection 0) (.projection 2)) (ys 3) (numeral 1) (ys 2) xx
    (hq 3) (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 1 xx) (hq 2)
  have hcut : Nonempty (Derivation body Theta
      (programGraph (.composition Program.succ (fun _ : Fin 1 => .projection (4 : Fin 7)))
        (suc (cutoff.relabel j)) xx)) :=
    unaryValue Program.succ (.projection (4 : Fin 7)) (suc (cutoff.relabel j))
    (cutoff.relabel j) xx (successorValue (Fin.cons (cutoff.relabel j) Fin.elim0)) (projectionValue 4 xx)
  have erased : Nonempty (Derivation body Theta
      (graph3 OriginalRawSyntaxTransport.eraseRaw (ys 4) (erasedType.relabel j)
        (suc (cutoff.relabel j)) (childRaw.relabel j))) :=
    compositionRecover OriginalRawSyntaxTransport.eraseRaw
      ![.projection 3,.composition .succ (fun _ : Fin 1 => .projection 4),.projection 2]
      (ys 4) xx ![erasedType.relabel j,suc (cutoff.relabel j),childRaw.relabel j] (hq 4)
      (fun i => Fin.cases (projectionValue 3 xx) (Fin.cases hcut
        (Fin.cases (projectionValue 2 xx) (fun k => Fin.elim0 k))) i)
  have childOut := binaryRecover InternalPairing.pairing (.projection 1) (queries 4)
    (ys 5) (codomain.relabel j) (ys 4) xx (hq 5) (projectionValue 1 xx) (hq 4)
  have innerOut := binaryRecover InternalPairing.pairing (.projection 0) (queries 4)
    (ys 6) (domain.relabel j) (ys 4) xx (hq 6) (projectionValue 0 xx) (hq 4)
  have rawOut := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 7 1)
    (queries 6) (ys 7) (numeral 1) (ys 6) xx
    (hq 7) (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 1 xx) (hq 6)
  have childGamma := binaryRecover InternalListCodec.consCode (.projection 0) (.projection 5)
    (ys 8) (domain.relabel j) (gamma.relabel j) xx (hq 8) (projectionValue 0 xx) (projectionValue 5 xx)
  have childExtended := binaryRecover InternalListCodec.consCode (.projection 0) (.projection 6)
    (ys 9) (domain.relabel j) (extended.relabel j) xx (hq 9) (projectionValue 0 xx) (projectionValue 6 xx)
  have parent := OriginalLambdaConstructorGraphSupportProof.packedOuter (s.relabel j)
    (domain.relabel j) (codomain.relabel j) (childRaw.relabel j) (ys 0) (ys 2) (ys 3)
    arrow inner raw hp'
  have coords := andIntro arrow (andIntro child (andIntro inner (andIntro raw parent)))
  have premise := andIntro coords (andIntro erased (andIntro childOut (andIntro innerOut
    (andIntro rawOut (andIntro he' (andIntro hc' (andIntro childGamma childExtended)))))))
  obtain ⟨law⟩ := OriginalLambdaErasureSquareProof.actualOriginalLambdaErasureCoordinateSquare
    body beta Theta (s.relabel j) (out.relabel j) (ys 1) (ys 5)
    (domain.relabel j) (codomain.relabel j) (ys 0) (ys 3) (childRaw.relabel j) (ys 2)
    (ys 4) (ys 6) (ys 7) (erasedType.relabel j) (cutoff.relabel j)
    (gamma.relabel j) (extended.relabel j) (ys 8) (ys 9)
  obtain ⟨premise⟩ := premise
  have result := Derivation.implicationElimination law premise
  have fields := OriginalLambdaConstructorGraphSupportProof.selectorsAtPairs (s.relabel j)
    (domain.relabel j) (childRaw.relabel j) (ys 0) (ys 2) (ys 3) inner raw parent
  have bodyCode := OriginalLambdaConstructorGraphSupportProof.bodyCodeValue (ys 1)
    (codomain.relabel j) (s.relabel j) (childRaw.relabel j)
    child (andRight (andRight (andRight fields)))
  exact consume beta j Theta (ys 1) (ys 5) (ys 8) (ys 9) hj (andIntro bodyCode ⟨result⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareQueryProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareQueryProof.actualOriginalLambdaErasureSquareQuery
