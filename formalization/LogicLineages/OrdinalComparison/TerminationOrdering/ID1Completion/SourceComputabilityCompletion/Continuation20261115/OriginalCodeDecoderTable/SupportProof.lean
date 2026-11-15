module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalListCodecSupportProof OriginalLambdaConstructorGraphSyntaxProof
open InternalRecursionGraphStepSyntaxProof InternalRawListRecursionSupportProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem succProjection {k : Nat} (i : Fin k) (xs : Fin k → OTerm alpha) :
    Nonempty (Derivation body Delta (programGraph (succOf (.projection i)) (suc (xs i)) xs)) :=
  unaryValue .succ (.projection i) (suc (xs i)) (xs i) xs
    (InternalControlGraphSupportProof.successorValue (Fin.cons (xs i) Fin.elim0)) (projectionValue i xs)

theorem baseRecover (n : Nat) (previous value output : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 (OriginalCodeDecoderStep.step n) value previous z)))
    (ho : Nonempty (Derivation body Delta (graph2 (nextRow n) output z previous))) :
    Nonempty (Derivation body Delta (consGraph output value z)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons previous Fin.elim0
  let cell : Program 1 := .composition (OriginalCodeDecoderStep.step n) ![.projection 0,constant 1 0]
  have hc : Nonempty (Derivation body Delta (programGraph cell value xs)) :=
    binaryValue (OriginalCodeDecoderStep.step n) (.projection 0) (constant 1 0) value previous z xs hv
      (projectionValue 0 xs) (constantValue 0 xs)
  apply InternalAcceptanceSupportProof.programCases (rowBase n) xs _
  intro beta j Theta base hj hb
  simp only [consGraphRename,zRelabel]
  have hv' := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  simp only [InternalControlGraphSupportProof.programRename,InternalRecursionGraphStepSyntaxProof.consTermRename,
    InternalControlGraphSupportProof.emptyRename] at hv'
  have ho' := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
  simp only [graph2Rename,zRelabel] at ho'
  simp only [xs,InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename] at hb
  let xx : Fin 1 → OTerm beta := Fin.cons (previous.relabel j) Fin.elim0
  have hz := recursionZeroValue (rowBase n) (rowStep n) base xx hb
  have he := valueUnique (nextRow n) base (output.relabel j)
    (Fin.cons z xx) hz ho'
  have hb' := outputTransport (rowBase n) base (output.relabel j) xx he hb
  exact binaryRecover InternalListCodec.consCode cell (constant 1 0) (output.relabel j) (value.relabel j) z xx
    hb' hv' (constantValue 0 xx)

theorem singletonValue (n : Nat) (count front previous value singleton : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 (OriginalCodeDecoderStep.step n) value previous (suc count))))
    (hc : Nonempty (Derivation body Delta (consGraph singleton value z))) :
    Nonempty (Derivation body Delta (programGraph
      (.composition InternalListCodec.consCode
        ![.composition (OriginalCodeDecoderStep.step n) ![.projection 2,succOf (.projection 0)],constant 3 0])
      singleton (Fin.cons count (Fin.cons front (Fin.cons previous Fin.elim0))))) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons count (Fin.cons front (Fin.cons previous Fin.elim0))
  let cell : Program 3 := .composition (OriginalCodeDecoderStep.step n) ![.projection 2,succOf (.projection 0)]
  have hcell : Nonempty (Derivation body Delta (programGraph cell value xs)) :=
    binaryValue (OriginalCodeDecoderStep.step n) (.projection 2) (succOf (.projection 0)) value previous (suc count) xs
      hv (projectionValue 2 xs) (succProjection 0 xs)
  exact binaryValue InternalListCodec.consCode cell (constant 3 0) singleton value z xs hc hcell (constantValue 0 xs)

theorem appendRecover (n : Nat) (count front previous value singleton output : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 (nextRow n) front count previous)))
    (ho : Nonempty (Derivation body Delta (graph2 (nextRow n) output (suc count) previous)))
    (hv : Nonempty (Derivation body Delta (graph2 (OriginalCodeDecoderStep.step n) value previous (suc count))))
    (hc : Nonempty (Derivation body Delta (consGraph singleton value z))) :
    Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append output front singleton)) := by
  have ht := recursionRecover (rowBase n) (rowStep n) output front count (Fin.cons previous Fin.elim0) hp ho
  let xs : Fin 3 → OTerm alpha := Fin.cons count (Fin.cons front (Fin.cons previous Fin.elim0))
  let single : Program 3 := .composition InternalListCodec.consCode
    ![.composition (OriginalCodeDecoderStep.step n) ![.projection 2,succOf (.projection 0)],constant 3 0]
  exact binaryRecover InternalApplicationValidityStackAppend.append (.projection 1) single output front singleton xs ht
    (projectionValue 1 xs) (singletonValue n count front previous value singleton hv hc)

theorem rowCases (n : Nat) (count previous : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (front value singleton : OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 (nextRow n) front (count.relabel j) (previous.relabel j))) →
      Nonempty (Derivation body Theta (graph2 (OriginalCodeDecoderStep.step n) value (previous.relabel j) (suc (count.relabel j)))) →
      Nonempty (Derivation body Theta (consGraph singleton value z)) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  let cell : Program 2 := .composition (OriginalCodeDecoderStep.step n) ![.projection 1,succOf (.projection 0)]
  let single : Program 2 := .composition InternalListCodec.consCode ![cell,constant 2 0]
  let qs : Fin 3 → Program 2 := ![nextRow n,cell,single]
  let xs : Fin 2 → OTerm alpha := Fin.cons count (Fin.cons previous Fin.elim0)
  apply queryCases qs xs psi
  intro beta j ys Theta hj hq
  let xx : Fin 2 → OTerm beta := Fin.cons (count.relabel j) (Fin.cons (previous.relabel j) Fin.elim0)
  have he : (fun i => (xs i).relabel j) = xx := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  rw [he] at hq
  have hv := binaryRecover (OriginalCodeDecoderStep.step n) (.projection 1) (succOf (.projection 0))
    (ys 1) (previous.relabel j) (suc (count.relabel j)) xx (hq 1) (projectionValue 1 xx) (succProjection 0 xx)
  have hc := binaryRecover InternalListCodec.consCode cell (constant 2 0) (ys 2) (ys 1) z xx
    (hq 2) (hq 1) (constantValue 0 xx)
  exact next beta j Theta (ys 0) (ys 1) (ys 2) hj (hq 0) hv hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.SupportProof
