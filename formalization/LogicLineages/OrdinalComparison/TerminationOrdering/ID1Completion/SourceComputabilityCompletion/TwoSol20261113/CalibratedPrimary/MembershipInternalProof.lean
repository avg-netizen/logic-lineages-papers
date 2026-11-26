module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHeadClassNumberInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalAcceptanceConjunctionProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalEqualityTestCompositionProof (equalityOfEqual)
open OriginalVariableDecoderEqualityProof (equalityReject)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Membership
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem stepHit (head rest needle : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn head needle))) :
    Nonempty (Derivation body Delta (graph3 containsStep (suc z) head rest needle)) := by
  let xs : Fin 3 → OTerm alpha := ![head,rest,needle]
  let control : Program 3 := .composition InternalEqualityTest.equalityTest ![.projection 0,.projection 2]
  have hc := binaryValue InternalEqualityTest.equalityTest (.projection 0) (.projection 2)
    (suc z) head needle xs (equalityOfEqual head needle he) (projectionValue 0 xs) (projectionValue 2 xs)
  exact successorBranchIntro control (.projection 1) (InternalLessThan.constantOne 3)
    (suc z) z xs hc (InternalLessThanSupportProof.oneConstantValue xs)

theorem stepMiss (head rest needle : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn head needle).not)) :
    Nonempty (Derivation body Delta (graph3 containsStep rest head rest needle)) := by
  let xs : Fin 3 → OTerm alpha := ![head,rest,needle]
  let control : Program 3 := .composition InternalEqualityTest.equalityTest ![.projection 0,.projection 2]
  have hc := binaryValue InternalEqualityTest.equalityTest (.projection 0) (.projection 2)
    z head needle xs (equalityReject head needle he) (projectionValue 0 xs) (projectionValue 2 xs)
  exact zeroBranchIntro control (.projection 1) (InternalLessThan.constantOne 3)
    rest xs hc (projectionValue 1 xs)

theorem containsNil (needle : OTerm alpha) :
    Nonempty (Derivation body Delta (graph2 contains z z needle)) :=
  InternalRawListRecursionProof.nilValue (InternalAcceptance.constantZero 1) containsStep
    z (Fin.cons needle Fin.elim0) (constantZeroValue _)

theorem containsHit (code head tail needle : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
    (he : Nonempty (Derivation body Delta (equal head needle))) :
    Nonempty (Derivation body Delta (graph2 contains (suc z) code needle)) := by
  rw [equalEqn] at he
  apply programCases contains (Fin.cons tail (Fin.cons needle Fin.elim0)) _
  intro beta j Theta rest hj hr
  simp only [graph2Rename,sucRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at hr
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  have he' := renameInto he j Theta hj
  rw [eqnRelabel] at he'
  exact InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 1) containsStep
    (code.relabel j) (head.relabel j) (tail.relabel j) rest (suc z)
    (Fin.cons (needle.relabel j) Fin.elim0) hc' hr
    (stepHit (head.relabel j) rest (needle.relabel j) he')

theorem containsMiss (code head tail needle out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
    (he : Nonempty (Derivation body Delta (equal head needle).not))
    (hr : Nonempty (Derivation body Delta (graph2 contains out tail needle))) :
    Nonempty (Derivation body Delta (graph2 contains out code needle)) := by
  rw [equalEqn] at he
  exact InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 1) containsStep
    code head tail out out (Fin.cons needle Fin.elim0) hc hr (stepMiss head out needle he)

theorem actualInternalContains : MembershipTargets.ActualInternalContains :=
  ⟨fun _ _ _ needle => containsNil needle,
    fun _ _ _ code head tail needle hc he => containsHit code head tail needle hc he,
    fun _ _ _ code head tail needle out hc he hr => containsMiss code head tail needle out hc he hr⟩

theorem actualInternalClassIntroduction : MembershipTargets.ActualInternalClassIntroduction := by
  intro T L D body alpha Delta seed candidate parameter list needle hT hL hD hmember
  let xs : Fin 3 → OTerm alpha := ![seed,candidate,parameter]
  let target : Program 3 := .composition T ![.projection 1,.projection 2]
  let values : Program 3 := .composition L ![.projection 0,.projection 2]
  let decoded : Program 3 := .composition D ![.projection 1,.projection 2]
  have ht := binaryValue T (.projection 1) (.projection 2) (suc z) candidate parameter xs
    hT (projectionValue 1 xs) (projectionValue 2 xs)
  have hl := binaryValue L (.projection 0) (.projection 2) list seed parameter xs
    hL (projectionValue 0 xs) (projectionValue 2 xs)
  have hd := binaryValue D (.projection 1) (.projection 2) needle candidate parameter xs
    hD (projectionValue 1 xs) (projectionValue 2 xs)
  have hm := binaryValue contains values decoded (suc z) list needle xs hmember hl hd
  exact conjunctionAccept target (.composition contains ![values,decoded]) xs ht hm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipInternalProof
