module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.ComputabilityLeastTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSpineMeasureEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineRepresentativeEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterTypedProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineBottomSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open Source (Ty)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalTagArithmeticSyntaxProof (OTerm z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open SourceComputabilityCompletion TypedSpine
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- Recover the literal original Object pair from its actual constructor
   graph. The Gamma input is an arbitrary symbolic code. -/
theorem bottomObjectPair (tau : Ty) (object gamma : OTerm α)
    (hb : Nonempty (Derivation body Delta
      (ComputabilityLeast.bottomGraph object
        (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) gamma))) :
    Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing object gamma (BottomSource.bottomTerm tau))) := by
  let typ : OTerm α := numeral (NumberedLeastCodeRepresentative.typeNumber tau)
  let xs : Fin 2 → OTerm α := Fin.cons typ (Fin.cons gamma Fin.elim0)
  have hcode := BottomSourceProof.bottomCodeAtNumeral (body := body) (Gamma := Delta) tau
  have hp := unaryValue BottomRepresentative.bottomCode (.projection (0 : Fin 2))
    (BottomSource.bottomTerm tau) typ xs hcode (projectionValue 0 xs)
  exact binaryRecover InternalPairing.pairing (.projection (1 : Fin 2))
    (.composition BottomRepresentative.bottomCode (fun _ : Fin 1 => .projection 0))
    object gamma (BottomSource.bottomTerm tau) xs hb (projectionValue 1 xs) hp

/-- A closed numeric computation on the literal packed bottom. Its use in
   open derivations below goes through the original numeral proof supplier. -/
theorem bottomMeasureEvaluation (tau : Ty) :
    evaluate BottomSpineMeasure.measure (List.Vector.ofFn ![BottomSource.bottomNumber tau]) =
      Nat.pair 1 0 := by
  rw [BottomSpineMeasureEvaluationProof.measureEvaluation,
    BottomSpineMeasureEvaluationProof.foldRecurrence]
  simp [InternalApplicationValidityStack.tagValue,
    InternalApplicationValidityStack.payloadValue, BottomSource.bottomNumber]

theorem bottomPayloadMarked (tau : Ty) :
    Nonempty (Derivation body Delta
      (BottomSpineMeasure.graph (numeral (Nat.pair 1 0)) (BottomSource.bottomTerm tau))) :=
  BottomSourceClosedProof.numeralGraph1 BottomSpineMeasure.measure
    (BottomSource.bottomNumber tau) (Nat.pair 1 0) (bottomMeasureEvaluation tau)

theorem bottomObjectMarked (tau : Ty) (object gamma : OTerm α)
    (hb : Nonempty (Derivation body Delta
      (ComputabilityLeast.bottomGraph object
        (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) gamma))) :
    Nonempty (Derivation body Delta (marked object (numeral (Nat.pair 1 0)) (numeral 0))) := by
  have hp := bottomObjectPair tau object gamma hb
  have hr := pairRight object gamma (BottomSource.bottomTerm tau) hp
  have hm := GlobalSourceSpineMeasureProof.objectMeasureValue object
    (BottomSource.bottomTerm tau) (numeral (Nat.pair 1 0)) hr (bottomPayloadMarked tau)
  have pairMark := BottomSourceClosedProof.numeralPair (body := body) (Delta := Delta) (α := α) 1 0
  exact andIntro hm (andIntro
    (pairLeft (numeral (Nat.pair 1 0)) (numeral 1) (numeral 0) pairMark)
    (pairRight (numeral (Nat.pair 1 0)) (numeral 1) (numeral 0) pairMark))

/-- Actual outer typedness of the literal bottom at the internally bound
   pair(context,Gamma). The exact selected Data is normalized only once. -/
theorem runtimeBottomTyped (n : Nat) (arity : Fin n → Nat) (base : Data)
    (hbase : InternalOriginalUniformDescentSelection.Calibrated n arity base)
    (window : Program 1) (hwindow : Path.windowCalibrated n window)
    (oldComp : JointGammaComputability.Data) (oldVertex oldResult : Program 5)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) (tau : Ty) (htau : tau ∈ S)
    (object gamma parameter : OTerm α)
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter
        (numeral (OrdinaryArithmeticQuotient.contextCode symbols S table)) gamma)))
    (hb : Nonempty (Derivation body Delta
      (ComputabilityLeast.bottomGraph object
        (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) gamma))) :
    Nonempty (Derivation body Delta
      (InternalComputabilityApplication.typed
        (OuterSelection.computability oldComp base window oldVertex oldResult)
        tau (numeral (OrdinaryArithmeticQuotient.contextCode symbols S table)) object)) := by
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  have hspine := SpineRepresentativeEvaluationProof.actualOriginalSpineRepresentativeCalibration
    n arity base window hbase hwindow
  have hraw := BottomSourceProof.runtimeTypedBottom n arity
    (SpineRepresentative.baseData base window) window hspine hwindow
    symbols S table hS tau htau parameter gamma hp
  have hobject := bottomObjectPair tau object gamma hb
  have hwindowGraph := BottomSourceClosedProof.numeralGraph1 (body := body) (Delta := Delta)
    (α := α) window context 1
    (BottomSourceClosedProof.closedWindowValue n window hwindow symbols S table hS)
  exact OuterTypedProof.typedAccept oldComp (OuterSelection.data base window) window
    oldVertex oldResult context (numeral (NumberedLeastCodeRepresentative.typeNumber tau))
    object gamma (BottomSource.bottomTerm tau) parameter hwindowGraph
    (pairLeft object gamma (BottomSource.bottomTerm tau) hobject)
    (pairRight object gamma (BottomSource.bottomTerm tau) hobject) hp hraw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineBottomSupportProof
