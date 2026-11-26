module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaMachineProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenLambdaProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBetaInstallationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaOpenRowsProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue successorValue valueUnique)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (consOfGraph)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralBetaLeafProof (rawLambdaShape)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralSingletonDepthNumericProof (zeroDepthInstance)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (singletonBound)
open NumberedWindowInternalLiteralSingletonBoundOpenLambdaProof (exact_OpenSingletonBoundLambda)
open NumberedWindowInternalLiteralSingletonBetaInstallationProof (exact_OpenZeroDepthInstance)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The literal shape test accepts an open packed lambda node, and both
selectors return its type and body fields. -/
theorem exact_OpenLambdaRead (ty b : OTerm α) :
    D B Γ (unary rawLambdaShape (suc z) (rawLambdaTerm ty b)) ∧
    D B Γ (unary (field 0) ty (rawLambdaTerm ty b)) ∧
    D B Γ (unary (field 1) b (rawLambdaTerm ty b)) := by
  let q := rawLambdaTerm ty b
  have tag : D B Γ (unary (literal 1 2) (numeral 2) q) := literalGraph 2 ![q]
  have report := packedNode (literal 1 2) (numeral 2) [ty,b] tag
  exact ⟨report.1,report.2.1,report.2.2.1⟩

/-- Child composition with the explicit binder bump. A graph of the
fallback on `[a,suc d,b]` is the graph of the actual child call on the
parent tape `[a,d,λ ty. b]`. The output is arbitrary, so this also
transports a failing child. -/
theorem exact_OpenLambdaChildCall (U : Program 3) (a d ty b out : OTerm α)
    (child : D B Γ (programGraph U out ![a,suc d,b])) :
    D B Γ (programGraph (lambdaChild U) out ![a,d,rawLambdaTerm ty b]) := by
  let q := rawLambdaTerm ty b
  let xs : Fin 3 → OTerm α := ![a,d,q]
  have rows := exact_OpenLambdaRead (B := B) (Γ := Γ) ty b
  have depth : D B Γ (programGraph binderDepth (suc d) xs) := by
    apply compositionValue .succ (fun _ : Fin 1 => .projection 1) (suc d) xs ![d]
      (successorValue ![d])
    intro k
    obtain rfl := Fin.eq_zero k
    exact projectionValue 1 xs
  have body : D B Γ (programGraph lambdaNodeBody b xs) := onTape (field 1) 2 b xs rows.2.2
  apply compositionValue U ![.projection 0,binderDepth,lambdaNodeBody] out xs ![a,suc d,b] child
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · exact projectionValue 0 xs
  · refine Fin.cases ?_ (fun l => ?_) j
    · exact depth
    · obtain rfl := Fin.eq_zero l
      exact body

/-- The exact emitter. From a successor-packed child output `suc b'` at
the bumped depth, the actual lambda instance rebuilds the literal node
with the original type field and the child code `b'`. -/
theorem exact_OpenLambdaInstance (U : Program 3) (a d ty b b' : OTerm α)
    (child : D B Γ (programGraph U (suc b') ![a,suc d,b])) :
    D B Γ (programGraph (lambdaInstance U) (suc (rawLambdaTerm ty b'))
      ![a,d,rawLambdaTerm ty b]) := by
  let q := rawLambdaTerm ty b
  let xs : Fin 3 → OTerm α := ![a,d,q]
  have rows := exact_OpenLambdaRead (B := B) (Γ := Γ) ty b
  have called : D B Γ (programGraph (lambdaChild U) (suc b') xs) :=
    exact_OpenLambdaChildCall U a d ty b (suc b') child
  have stripped : D B Γ (programGraph (lambdaChildCode U) b' xs) := by
    apply compositionValue predecessor (fun _ : Fin 1 => lambdaChild U) b' xs ![suc b']
      (predecessorSuccessor b')
    intro k
    obtain rfl := Fin.eq_zero k
    exact called
  have typeField : D B Γ (programGraph lambdaNodeType ty xs) := onTape (field 0) 2 ty xs rows.2.1
  have tailGraph := consOfGraph (lambdaChildCode U) (constantZero 3) b' z xs stripped
    (constantZeroValue xs)
  have bodyGraph := consOfGraph lambdaNodeType (consOf (lambdaChildCode U) (constantZero 3))
    ty (rawCons b' z) xs typeField tailGraph
  have code : D B Γ (programGraph (lambdaRebuiltCode U) (rawLambdaTerm ty b') xs) :=
    consOfGraph (literal 3 2) (consOf lambdaNodeType (consOf (lambdaChildCode U) (constantZero 3)))
      (numeral 2) (rawCons ty (rawCons b' z)) xs (literalGraph 2 xs) bodyGraph
  have rebuilt : D B Γ (programGraph (lambdaRebuilt U) (suc (rawLambdaTerm ty b')) xs) := by
    apply compositionValue .succ (fun _ : Fin 1 => lambdaRebuiltCode U)
      (suc (rawLambdaTerm ty b')) xs ![rawLambdaTerm ty b'] (successorValue ![rawLambdaTerm ty b'])
    intro k
    obtain rfl := Fin.eq_zero k
    exact code
  exact successorBranchIntro (lambdaChild U) (constantZero 3) (lambdaRebuilt U)
    (suc (rawLambdaTerm ty b')) b' xs called rebuilt

/-- The lambda shape test is a positive hit, so the dispatch takes the
physical lambda instance rather than the fallback. -/
theorem exact_OpenSingletonLambdaDispatch (U : Program 3) (a d ty b b' : OTerm α)
    (child : D B Γ (programGraph U (suc b') ![a,suc d,b])) :
    D B Γ (programGraph (singletonLambdaDispatch U) (suc (rawLambdaTerm ty b'))
      ![a,d,rawLambdaTerm ty b]) := by
  let xs : Fin 3 → OTerm α := ![a,d,rawLambdaTerm ty b]
  have isLambda : D B Γ (bit (onRaw rawLambdaShape 2) xs) :=
    onTape rawLambdaShape 2 (suc z) xs (exact_OpenLambdaRead ty b).1
  exact successorBranchIntro (onRaw rawLambdaShape 2) U (lambdaInstance U)
    (suc (rawLambdaTerm ty b')) z xs isLambda (exact_OpenLambdaInstance U a d ty b b' child)

/-- Lambda row of the installed program. Both syntax premises are the
original positive hits on the inserted code and on the whole node; the
only premise about the body is an actual open graph of the fallback at
depth `suc d`. Nothing is assumed about how that graph was obtained and
no numeric fit of `U` or of `singletonLambda` is used. -/
theorem exact_OpenSingletonLambdaRow (V : Program 1) (H : Program 2) (U : Program 3)
    (a d ty b b' : OTerm α)
    (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (rawLambdaTerm ty b)))
    (child : D B Γ (programGraph U (suc b') ![a,suc d,b])) :
    D B Γ (programGraph (singletonLambda V H U) (suc (rawLambdaTerm ty b'))
      ![a,d,rawLambdaTerm ty b]) :=
  exact_OpenSingletonBoundLambda V H (singletonLambdaDispatch U) a d ty b
    (suc (rawLambdaTerm ty b')) inserted typedNode
    (exact_OpenSingletonLambdaDispatch U a d ty b b' child)

/-- The row composes with itself through the fallback slot: two nested
binders use the innermost child at depth `suc (suc d)`. The inner node's
syntax hit is a separate premise, as the compiled guard checks it again. -/
theorem exact_OpenSingletonLambdaNested (V : Program 1) (H : Program 2) (U : Program 3)
    (a d outerTy innerTy b b' : OTerm α)
    (inserted : D B Γ (unary V (suc z) a))
    (outerNode : D B Γ (unary V (suc z) (rawLambdaTerm outerTy (rawLambdaTerm innerTy b))))
    (innerNode : D B Γ (unary V (suc z) (rawLambdaTerm innerTy b)))
    (child : D B Γ (programGraph U (suc b') ![a,suc (suc d),b])) :
    D B Γ (programGraph (singletonLambda V H (singletonLambda V H U))
      (suc (rawLambdaTerm outerTy (rawLambdaTerm innerTy b')))
      ![a,d,rawLambdaTerm outerTy (rawLambdaTerm innerTy b)]) :=
  exact_OpenSingletonLambdaRow V H (singletonLambda V H U) a d outerTy
    (rawLambdaTerm innerTy b) (rawLambdaTerm innerTy b') inserted outerNode
    (exact_OpenSingletonLambdaRow V H U a (suc d) innerTy b b' inserted innerNode child)

/-- Beta installation. When the discharged body is itself a lambda, the
zero-depth beta instance returns the rebuilt node whose child was
computed at literal depth one. -/
theorem exact_OpenBetaLambdaBody (V : Program 1) (H : Program 2) (U : Program 3)
    (a ty b b' : OTerm α)
    (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (rawLambdaTerm ty b)))
    (child : D B Γ (programGraph U (suc b') ![a,suc z,b])) :
    D B Γ (programGraph (zeroDepthInstance (singletonLambda V H U))
      (suc (rawLambdaTerm ty b')) ![a,rawLambdaTerm ty b]) :=
  exact_OpenZeroDepthInstance (singletonLambda V H U) a (rawLambdaTerm ty b)
    (suc (rawLambdaTerm ty b'))
    (exact_OpenSingletonLambdaRow V H U a z ty b b' inserted typedNode child)

/-- The premise an accepted beta leaf supplies is a graph of its
instance program with output `suc r`. On a lambda body that output is
the rebuilt node, by functionality of the same program graph. -/
theorem exact_OpenBetaLambdaBodyTarget (V : Program 1) (H : Program 2) (U : Program 3)
    (a ty b b' r : OTerm α)
    (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (rawLambdaTerm ty b)))
    (child : D B Γ (programGraph U (suc b') ![a,suc z,b]))
    (held : D B Γ (programGraph (zeroDepthInstance (singletonLambda V H U)) (suc r)
      ![a,rawLambdaTerm ty b])) :
    D B Γ (eqn (suc r) (suc (rawLambdaTerm ty b'))) :=
  valueUnique (zeroDepthInstance (singletonLambda V H U)) (suc r) (suc (rawLambdaTerm ty b'))
    ![a,rawLambdaTerm ty b] held (exact_OpenBetaLambdaBody V H U a ty b b' inserted typedNode child)

#print axioms exact_OpenLambdaRead
#print axioms exact_OpenLambdaChildCall
#print axioms exact_OpenLambdaInstance
#print axioms exact_OpenSingletonLambdaDispatch
#print axioms exact_OpenSingletonLambdaRow
#print axioms exact_OpenSingletonLambdaNested
#print axioms exact_OpenBetaLambdaBody
#print axioms exact_OpenBetaLambdaBodyTarget
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaOpenRowsProof
