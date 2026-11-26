module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaOpenRowsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootTapeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaOpenCasesProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof
  (zeroBranchIntro successorBranchIntro zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalSparseRawRunRootTapeProof (rejectLeft rejectRight)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralBetaLeafProof (rawLambdaShape)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralSingletonAtomsNumericProof (singletonSyntax singletonAtomicDispatch)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (singletonBound singletonBoundDispatch)
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof (exact_OpenLiteralOtherTag)
open NumberedWindowInternalLiteralSingletonBoundOpenLambdaProof
open NumberedWindowInternalLiteralSingletonLambdaMachineProof
open NumberedWindowInternalLiteralSingletonLambdaOpenRowsProof
  (exact_OpenLambdaRead exact_OpenLambdaChildCall)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- On a packed lambda node the dispatch is the lambda instance, for any
output. This is the positive selector law of the written dispatch. -/
theorem exact_OpenSingletonLambdaDispatchHit (U : Program 3) (a d ty b out : OTerm α)
    (run : D B Γ (programGraph (lambdaInstance U) out ![a,d,rawLambdaTerm ty b])) :
    D B Γ (programGraph (singletonLambdaDispatch U) out ![a,d,rawLambdaTerm ty b]) := by
  let xs : Fin 3 → OTerm α := ![a,d,rawLambdaTerm ty b]
  have isLambda : D B Γ (bit (onRaw rawLambdaShape 2) xs) :=
    onTape rawLambdaShape 2 (suc z) xs (exact_OpenLambdaRead ty b).1
  exact successorBranchIntro (onRaw rawLambdaShape 2) U (lambdaInstance U) out z xs isLambda run

theorem exact_OpenSingletonLambdaDispatchHitRecover (U : Program 3) (a d ty b out : OTerm α)
    (held : D B Γ (programGraph (singletonLambdaDispatch U) out ![a,d,rawLambdaTerm ty b])) :
    D B Γ (programGraph (lambdaInstance U) out ![a,d,rawLambdaTerm ty b]) := by
  let xs : Fin 3 → OTerm α := ![a,d,rawLambdaTerm ty b]
  have isLambda : D B Γ (bit (onRaw rawLambdaShape 2) xs) :=
    onTape rawLambdaShape 2 (suc z) xs (exact_OpenLambdaRead ty b).1
  exact successorBranchElim (onRaw rawLambdaShape 2) U (lambdaInstance U) out z xs isLambda held

/-- Zero child. A failing fallback graph at the bumped depth makes the
written lambda instance return zero; the emitter is not run. -/
theorem exact_OpenLambdaInstanceZero (U : Program 3) (a d ty b : OTerm α)
    (child : D B Γ (programGraph U z ![a,suc d,b])) :
    D B Γ (programGraph (lambdaInstance U) z ![a,d,rawLambdaTerm ty b]) := by
  let xs : Fin 3 → OTerm α := ![a,d,rawLambdaTerm ty b]
  exact zeroBranchIntro (lambdaChild U) (constantZero 3) (lambdaRebuilt U) z xs
    (exact_OpenLambdaChildCall U a d ty b z child) (constantZeroValue xs)

/-- Inversion of the zero branch by the selector law: with a failing
child, every output of the lambda instance is zero. -/
theorem exact_OpenLambdaInstanceZeroRecover (U : Program 3) (a d ty b out : OTerm α)
    (child : D B Γ (programGraph U z ![a,suc d,b]))
    (held : D B Γ (programGraph (lambdaInstance U) out ![a,d,rawLambdaTerm ty b])) :
    D B Γ (eqn out z) := by
  let xs : Fin 3 → OTerm α := ![a,d,rawLambdaTerm ty b]
  have failed : D B Γ (programGraph (constantZero 3) out xs) :=
    zeroBranchElim (lambdaChild U) (constantZero 3) (lambdaRebuilt U) out xs
      (exact_OpenLambdaChildCall U a d ty b z child) held
  exact valueUnique (constantZero 3) out z xs failed (constantZeroValue xs)

/-- Zero-child row of the installed program, behind both original
syntax hits. -/
theorem exact_OpenSingletonLambdaRowZero (V : Program 1) (H : Program 2) (U : Program 3)
    (a d ty b : OTerm α)
    (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (rawLambdaTerm ty b)))
    (child : D B Γ (programGraph U z ![a,suc d,b])) :
    D B Γ (programGraph (singletonLambda V H U) z ![a,d,rawLambdaTerm ty b]) :=
  exact_OpenSingletonBoundLambda V H (singletonLambdaDispatch U) a d ty b z inserted typedNode
    (exact_OpenSingletonLambdaDispatchHit U a d ty b z (exact_OpenLambdaInstanceZero U a d ty b child))

/-- Selector-law inversion of the whole lambda row: any output of the
installed program on a guarded lambda node is an output of the written
lambda instance. No premise about the child is used. -/
theorem exact_OpenSingletonLambdaRowRecover (V : Program 1) (H : Program 2) (U : Program 3)
    (a d ty b out : OTerm α)
    (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (rawLambdaTerm ty b)))
    (held : D B Γ (programGraph (singletonLambda V H U) out ![a,d,rawLambdaTerm ty b])) :
    D B Γ (programGraph (lambdaInstance U) out ![a,d,rawLambdaTerm ty b]) :=
  exact_OpenSingletonLambdaDispatchHitRecover U a d ty b out
    (exact_OpenSingletonBoundLambdaRecover V H (singletonLambdaDispatch U) a d ty b out
      inserted typedNode held)

theorem exact_OpenSingletonLambdaRowZeroRecover (V : Program 1) (H : Program 2) (U : Program 3)
    (a d ty b out : OTerm α)
    (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (rawLambdaTerm ty b)))
    (child : D B Γ (programGraph U z ![a,suc d,b]))
    (held : D B Γ (programGraph (singletonLambda V H U) out ![a,d,rawLambdaTerm ty b])) :
    D B Γ (eqn out z) :=
  exact_OpenLambdaInstanceZeroRecover U a d ty b out child
    (exact_OpenSingletonLambdaRowRecover V H U a d ty b out inserted typedNode held)

/-- Fall-through. On a packed node whose literal tag is not the lambda
tag, the shape test is physically rejected and the dispatch is the
fallback at the same depth. -/
theorem exact_OpenSingletonLambdaDispatchOtherTag (U : Program 3)
    (tag : Nat) (payload : List (OTerm α)) (a d out : OTerm α) (notLambda : tag ≠ 2)
    (computed : D B Γ (programGraph U out ![a,d,rawCons (numeral tag) (packedBody payload)])) :
    D B Γ (programGraph (singletonLambdaDispatch U) out
      ![a,d,rawCons (numeral tag) (packedBody payload)]) := by
  let xs : Fin 3 → OTerm α := ![a,d,rawCons (numeral tag) (packedBody payload)]
  have rejected : D B Γ (programGraph (onRaw rawLambdaShape 2) z xs) :=
    onTape rawLambdaShape 2 z xs (exact_OpenLiteralOtherTag 2 tag 2 payload notLambda)
  exact zeroBranchIntro (onRaw rawLambdaShape 2) U (lambdaInstance U) out xs rejected computed

theorem exact_OpenSingletonLambdaDispatchOtherTagRecover (U : Program 3)
    (tag : Nat) (payload : List (OTerm α)) (a d out : OTerm α) (notLambda : tag ≠ 2)
    (held : D B Γ (programGraph (singletonLambdaDispatch U) out
      ![a,d,rawCons (numeral tag) (packedBody payload)])) :
    D B Γ (programGraph U out ![a,d,rawCons (numeral tag) (packedBody payload)]) := by
  let xs : Fin 3 → OTerm α := ![a,d,rawCons (numeral tag) (packedBody payload)]
  have rejected : D B Γ (programGraph (onRaw rawLambdaShape 2) z xs) :=
    onTape rawLambdaShape 2 z xs (exact_OpenLiteralOtherTag 2 tag 2 payload notLambda)
  exact zeroBranchElim (onRaw rawLambdaShape 2) U (lambdaInstance U) out xs rejected held

/-- Fall-through row of the installed program: a guarded node with none
of the four physical tags is computed by the fallback at the same depth. -/
theorem exact_OpenSingletonLambdaOtherTag (V : Program 1) (H : Program 2) (U : Program 3)
    (tag : Nat) (payload : List (OTerm α)) (a d out : OTerm α)
    (notFree : tag ≠ 0) (notBound : tag ≠ 1) (notLambda : tag ≠ 2) (notBottom : tag ≠ 3)
    (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (rawCons (numeral tag) (packedBody payload))))
    (computed : D B Γ (programGraph U out ![a,d,rawCons (numeral tag) (packedBody payload)])) :
    D B Γ (programGraph (singletonLambda V H U) out
      ![a,d,rawCons (numeral tag) (packedBody payload)]) :=
  exact_OpenSingletonBoundOtherTag V H (singletonLambdaDispatch U) tag payload a d out
    notFree notBound notBottom inserted typedNode
    (exact_OpenSingletonLambdaDispatchOtherTag U tag payload a d out notLambda computed)

theorem exact_OpenSingletonLambdaOtherTagRecover (V : Program 1) (H : Program 2) (U : Program 3)
    (tag : Nat) (payload : List (OTerm α)) (a d out : OTerm α)
    (notFree : tag ≠ 0) (notBound : tag ≠ 1) (notLambda : tag ≠ 2) (notBottom : tag ≠ 3)
    (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (rawCons (numeral tag) (packedBody payload))))
    (held : D B Γ (programGraph (singletonLambda V H U) out
      ![a,d,rawCons (numeral tag) (packedBody payload)])) :
    D B Γ (programGraph U out ![a,d,rawCons (numeral tag) (packedBody payload)]) :=
  exact_OpenSingletonLambdaDispatchOtherTagRecover U tag payload a d out notLambda
    (exact_OpenSingletonBoundOtherTagRecover V H (singletonLambdaDispatch U) tag payload a d out
      notFree notBound notBottom inserted typedNode held)

/-- The two ways the original outer syntax guard rejects. -/
theorem exact_OpenSingletonSyntaxRejectInserted (V : Program 1) (a d q : OTerm α)
    (bad : D B Γ (unary V z a)) :
    D B Γ (programGraph (singletonSyntax V) z ![a,d,q]) :=
  rejectLeft (onRaw V 0) (onRaw V 2) ![a,d,q] (onTape V 0 z ![a,d,q] bad)

theorem exact_OpenSingletonSyntaxRejectNode (V : Program 1) (a d q : OTerm α)
    (good : D B Γ (unary V (suc z) a)) (bad : D B Γ (unary V z q)) :
    D B Γ (programGraph (singletonSyntax V) z ![a,d,q]) :=
  rejectRight (onRaw V 0) (onRaw V 2) ![a,d,q] (onTape V 0 (suc z) ![a,d,q] good)
    (onTape V 2 z ![a,d,q] bad)

/-- Off the guard the installed program returns zero for every slot
program: the fallback slot is never consulted. This is the object-level
reason a slot only needs to be correct on guarded tapes. -/
theorem exact_OpenSingletonBoundGuardZero (V : Program 1) (H : Program 2) (U : Program 3)
    (a d q : OTerm α)
    (rejected : D B Γ (programGraph (singletonSyntax V) z ![a,d,q])) :
    D B Γ (programGraph (singletonBound V H U) z ![a,d,q]) := by
  let xs : Fin 3 → OTerm α := ![a,d,q]
  let fallback := branch (singletonSyntax V) (constantZero 3) (singletonBoundDispatch H U)
  exact zeroBranchIntro (singletonSyntax V) (constantZero 3) (singletonAtomicDispatch fallback)
    z xs rejected (constantZeroValue xs)

theorem exact_OpenSingletonLambdaGuardZero (V : Program 1) (H : Program 2) (U : Program 3)
    (a d q : OTerm α)
    (rejected : D B Γ (programGraph (singletonSyntax V) z ![a,d,q])) :
    D B Γ (programGraph (singletonLambda V H U) z ![a,d,q]) :=
  exact_OpenSingletonBoundGuardZero V H (singletonLambdaDispatch U) a d q rejected

#print axioms exact_OpenSingletonLambdaDispatchHit
#print axioms exact_OpenSingletonLambdaDispatchHitRecover
#print axioms exact_OpenLambdaInstanceZero
#print axioms exact_OpenLambdaInstanceZeroRecover
#print axioms exact_OpenSingletonLambdaRowZero
#print axioms exact_OpenSingletonLambdaRowRecover
#print axioms exact_OpenSingletonLambdaRowZeroRecover
#print axioms exact_OpenSingletonLambdaDispatchOtherTag
#print axioms exact_OpenSingletonLambdaDispatchOtherTagRecover
#print axioms exact_OpenSingletonLambdaOtherTag
#print axioms exact_OpenSingletonLambdaOtherTagRecover
#print axioms exact_OpenSingletonSyntaxRejectInserted
#print axioms exact_OpenSingletonSyntaxRejectNode
#print axioms exact_OpenSingletonBoundGuardZero
#print axioms exact_OpenSingletonLambdaGuardZero
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaOpenCasesProof
