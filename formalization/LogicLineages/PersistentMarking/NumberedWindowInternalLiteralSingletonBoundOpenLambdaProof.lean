module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenRowsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenLambdaProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof
  (zeroBranchIntro successorBranchIntro zeroBranchElim successorBranchElim)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralAtomicRawGuardProof (freeTest bottomTest)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralSingletonAtomsNumericProof
open NumberedWindowInternalLiteralSingletonAtomsOpenProof (exact_OpenSingletonSyntax)
open NumberedWindowInternalLiteralSingletonBoundMachineProof
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Physical rejection of the three atomic dispatch tests on an open
packed node whose literal tag is none of free (0), bound (1), bottom (3).
Each rejection is the actual compiled test returning zero on the tape
slot holding the node; the payload is arbitrary and is never inspected. -/
theorem exact_OpenSingletonTagRejections (tag : Nat) (payload : List (OTerm α)) (a d : OTerm α)
    (notFree : tag ≠ 0) (notBound : tag ≠ 1) (notBottom : tag ≠ 3) :
    D B Γ (programGraph (onRaw freeTest 2) z ![a,d,rawCons (numeral tag) (packedBody payload)]) ∧
    D B Γ (programGraph (onRaw bottomTest 2) z ![a,d,rawCons (numeral tag) (packedBody payload)]) ∧
    D B Γ (programGraph (onRaw boundShape 2) z ![a,d,rawCons (numeral tag) (packedBody payload)]) := by
  let q := rawCons (numeral tag) (packedBody payload)
  let xs : Fin 3 → OTerm α := ![a,d,q]
  exact ⟨onTape freeTest 2 z xs (exact_OpenLiteralOtherTag 0 tag 2 payload notFree),
    onTape bottomTest 2 z xs (exact_OpenLiteralOtherTag 3 tag 1 payload notBottom),
    onTape boundShape 2 z xs (exact_OpenLiteralOtherTag 1 tag 2 payload notBound)⟩

/-- First non-atomic dispatch boundary. On an open packed node with a
non-atomic literal tag, an actual open graph of the fallback `U` on the
same tape `[a,d,node]` (same inserted code, same binder depth `d`)
transfers to the actual `singletonBound V H U` with the same output.
Both syntax guards are positive hits and are passed twice, exactly as in
the compiled program. `U` is an arbitrary program: nothing here uses or
asserts a numeric fit for `U`, and nothing is said about how `U`
computes on the node's children. -/
theorem exact_OpenSingletonBoundOtherTag (V : Program 1) (H : Program 2) (U : Program 3)
    (tag : Nat) (payload : List (OTerm α)) (a d out : OTerm α)
    (notFree : tag ≠ 0) (notBound : tag ≠ 1) (notBottom : tag ≠ 3)
    (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (rawCons (numeral tag) (packedBody payload))))
    (computed : D B Γ (programGraph U out ![a,d,rawCons (numeral tag) (packedBody payload)])) :
    D B Γ (programGraph (singletonBound V H U) out
      ![a,d,rawCons (numeral tag) (packedBody payload)]) := by
  let q := rawCons (numeral tag) (packedBody payload)
  let xs : Fin 3 → OTerm α := ![a,d,q]
  let fallback := branch (singletonSyntax V) (constantZero 3) (singletonBoundDispatch H U)
  have rejected := exact_OpenSingletonTagRejections (B := B) (Γ := Γ) tag payload a d
    notFree notBound notBottom
  have valid := exact_OpenSingletonSyntax V a d q inserted typedNode
  have selected : D B Γ (programGraph (singletonBoundDispatch H U) out xs) :=
    zeroBranchIntro (onRaw boundShape 2) U (boundInstance H) out xs rejected.2.2 computed
  have middle : D B Γ (programGraph fallback out xs) :=
    successorBranchIntro (singletonSyntax V) (constantZero 3) (singletonBoundDispatch H U)
      out z xs valid selected
  have dis : D B Γ (programGraph (singletonAtomicDispatch fallback) out xs) :=
    zeroBranchIntro (onRaw freeTest 2) (branch (onRaw bottomTest 2) fallback retainSingleton) retainSingleton
      out xs rejected.1
      (zeroBranchIntro (onRaw bottomTest 2) fallback retainSingleton out xs rejected.2.1 middle)
  exact successorBranchIntro (singletonSyntax V) (constantZero 3) (singletonAtomicDispatch fallback)
    out z xs valid dis

/-- Converse on the same tape: any output of the actual
`singletonBound V H U` on a guarded non-atomic node is an output of the
fallback `U` at the same depth. Only branch elimination is used; no
functionality or numeric calibration of `U` is assumed. -/
theorem exact_OpenSingletonBoundOtherTagRecover (V : Program 1) (H : Program 2) (U : Program 3)
    (tag : Nat) (payload : List (OTerm α)) (a d out : OTerm α)
    (notFree : tag ≠ 0) (notBound : tag ≠ 1) (notBottom : tag ≠ 3)
    (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (rawCons (numeral tag) (packedBody payload))))
    (held : D B Γ (programGraph (singletonBound V H U) out
      ![a,d,rawCons (numeral tag) (packedBody payload)])) :
    D B Γ (programGraph U out ![a,d,rawCons (numeral tag) (packedBody payload)]) := by
  let q := rawCons (numeral tag) (packedBody payload)
  let xs : Fin 3 → OTerm α := ![a,d,q]
  let fallback := branch (singletonSyntax V) (constantZero 3) (singletonBoundDispatch H U)
  have rejected := exact_OpenSingletonTagRejections (B := B) (Γ := Γ) tag payload a d
    notFree notBound notBottom
  have valid := exact_OpenSingletonSyntax V a d q inserted typedNode
  have dis : D B Γ (programGraph (singletonAtomicDispatch fallback) out xs) :=
    successorBranchElim (singletonSyntax V) (constantZero 3) (singletonAtomicDispatch fallback)
      out z xs valid held
  have inner : D B Γ (programGraph (branch (onRaw bottomTest 2) fallback retainSingleton) out xs) :=
    zeroBranchElim (onRaw freeTest 2) (branch (onRaw bottomTest 2) fallback retainSingleton)
      retainSingleton out xs rejected.1 dis
  have middle : D B Γ (programGraph fallback out xs) :=
    zeroBranchElim (onRaw bottomTest 2) fallback retainSingleton out xs rejected.2.1 inner
  have selected : D B Γ (programGraph (singletonBoundDispatch H U) out xs) :=
    successorBranchElim (singletonSyntax V) (constantZero 3) (singletonBoundDispatch H U)
      out z xs valid middle
  exact zeroBranchElim (onRaw boundShape 2) U (boundInstance H) out xs rejected.2.2 selected

/-- Literal lambda row: on a genuinely open packed lambda node the
actual `singletonBound` agrees with the same-depth fallback graph. The
binder depth `d` is the tape's own; no depth increment and no claim
about the body's substitution is made at this boundary. -/
theorem exact_OpenSingletonBoundLambda (V : Program 1) (H : Program 2) (U : Program 3)
    (a d ty body out : OTerm α)
    (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (rawLambdaTerm ty body)))
    (computed : D B Γ (programGraph U out ![a,d,rawLambdaTerm ty body])) :
    D B Γ (programGraph (singletonBound V H U) out ![a,d,rawLambdaTerm ty body]) :=
  exact_OpenSingletonBoundOtherTag V H U 2 [ty,body] a d out (by decide) (by decide) (by decide)
    inserted typedNode computed

theorem exact_OpenSingletonBoundLambdaRecover (V : Program 1) (H : Program 2) (U : Program 3)
    (a d ty body out : OTerm α)
    (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (rawLambdaTerm ty body)))
    (held : D B Γ (programGraph (singletonBound V H U) out ![a,d,rawLambdaTerm ty body])) :
    D B Γ (programGraph U out ![a,d,rawLambdaTerm ty body]) :=
  exact_OpenSingletonBoundOtherTagRecover V H U 2 [ty,body] a d out (by decide) (by decide) (by decide)
    inserted typedNode held

#print axioms exact_OpenSingletonTagRejections
#print axioms exact_OpenSingletonBoundOtherTag
#print axioms exact_OpenSingletonBoundOtherTagRecover
#print axioms exact_OpenSingletonBoundLambda
#print axioms exact_OpenSingletonBoundLambdaRecover
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenLambdaProof
