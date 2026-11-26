module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitAtomsMachineProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitAtomsOpenProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptance (branch)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralAtomicRawGuardProof (freeTest bottomTest)
open NumberedWindowInternalLiteralAtomicRawShapeProof (freeTerm bottomTerm freeReports)
open NumberedWindowInternalLiteralSingletonAtomsNumericProof
  (singletonSyntax retainSingleton singletonAtomicDispatch)
open NumberedWindowInternalLiteralSingletonAtomsOpenProof
  (exact_OpenSingletonSyntax exact_OpenSingletonRetain)
open NumberedWindowInternalLiteralSingletonBoundMachineProof
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof
open NumberedWindowInternalLiteralSingletonBoundOpenHitProof (exact_OpenSingletonBoundAtPositiveDepth)
open NumberedWindowInternalLiteralSingletonShiftHitMachineProof
open NumberedWindowInternalLiteralSingletonShiftHitOpenProof
  (exact_OpenShiftHitBound exact_OpenSingletonBoundShiftedBoundLiteral)
open NumberedWindowInternalLiteralSingletonShiftHitAtomsMachineProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- A three-slot program read on the replacement tape `[a,d,a]`. -/
theorem exact_OpenReplacementTape (P : Program 3) (a d out : OTerm α)
    (h : D B Γ (programGraph P out ![a,d,a])) :
    D B Γ (programGraph
      (Program.composition P (![.projection 0,.projection 1,.projection 0] : Fin 3 → Program 2))
      out ![a,d]) := by
  apply compositionValue P (![.projection 0,.projection 1,.projection 0] : Fin 3 → Program 2)
    out ![a,d] ![a,d,a] h
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · exact projectionValue (0 : Fin 2) ![a,d]
  · refine Fin.cases ?_ (fun l => ?_) j
    · exact projectionValue (1 : Fin 2) ![a,d]
    · obtain rfl := Fin.eq_zero l
      exact projectionValue (0 : Fin 2) ![a,d]

/-- The fallback slot is the supplied program on the first two slots. -/
theorem exact_OpenShiftHitFallback (H : Program 2) (a d q out : OTerm α)
    (h : D B Γ (programGraph H out ![a,d])) :
    D B Γ (programGraph (shiftHitFallback H) out ![a,d,q]) := by
  let xs : Fin 3 → OTerm α := ![a,d,q]
  apply compositionValue H (![.projection 0,.projection 1] : Fin 2 → Program 3) out xs ![a,d] h
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · exact projectionValue (0 : Fin 3) xs
  · obtain rfl := Fin.eq_zero j
    exact projectionValue (1 : Fin 3) xs

/-- The saved bound front passes a guarded non-bound replacement to its
fallback unchanged. -/
theorem exact_OpenShiftHitBoundPass (V : Program 1) (H : Program 2) (a d out : OTerm α)
    (typed : D B Γ (unary V (suc z) a))
    (notBound : D B Γ (unary boundShape z a))
    (h : D B Γ (programGraph H out ![a,d])) :
    D B Γ (programGraph (shiftHitBound V H) out ![a,d]) := by
  let xs : Fin 3 → OTerm α := ![a,d,a]
  have valid : D B Γ (bit (singletonSyntax V) xs) := exact_OpenSingletonSyntax V a d a typed typed
  have rejected : D B Γ (programGraph (onRaw boundShape 2) z xs) :=
    onTape boundShape 2 z xs notBound
  have passed : D B Γ (programGraph (shiftHitFallback H) out xs) :=
    exact_OpenShiftHitFallback H a d a out h
  have inner : D B Γ (programGraph
      (branch (onRaw boundShape 2) (shiftHitFallback H) shiftBoundRaised) out xs) :=
    zeroBranchIntro (onRaw boundShape 2) (shiftHitFallback H) shiftBoundRaised out xs
      rejected passed
  have dispatched : D B Γ (programGraph (shiftHitDispatch V H) out xs) :=
    successorBranchIntro (singletonSyntax V) (shiftHitFallback H)
      (branch (onRaw boundShape 2) (shiftHitFallback H) shiftBoundRaised) out z xs valid inner
  exact exact_OpenReplacementTape (shiftHitDispatch V H) a d out dispatched

/-- The atom front retains a typed open free literal; type and name are
arbitrary terms and nothing is assumed about `H`. -/
theorem exact_OpenShiftHitAtomsFree (V : Program 1) (H : Program 2) (t n d : OTerm α)
    (typed : D B Γ (unary V (suc z) (freeTerm t n))) :
    D B Γ (programGraph (shiftHitAtoms V H) (suc (freeTerm t n)) ![freeTerm t n,d]) := by
  let q := freeTerm t n
  let xs : Fin 3 → OTerm α := ![q,d,q]
  let U := shiftHitFallback H
  have valid : D B Γ (bit (singletonSyntax V) xs) := exact_OpenSingletonSyntax V q d q typed typed
  have isFree : D B Γ (bit (onRaw freeTest 2) xs) :=
    onTape freeTest 2 (suc z) xs (freeReports t n).1
  have dispatch : D B Γ (programGraph (singletonAtomicDispatch U) (suc q) xs) :=
    successorBranchIntro (onRaw freeTest 2) (branch (onRaw bottomTest 2) U retainSingleton)
      retainSingleton (suc q) z xs isFree (exact_OpenSingletonRetain q d q)
  have dispatched : D B Γ (programGraph (shiftAtomDispatch V H) (suc q) xs) :=
    successorBranchIntro (singletonSyntax V) U (singletonAtomicDispatch U) (suc q) z xs
      valid dispatch
  exact exact_OpenReplacementTape (shiftAtomDispatch V H) q d (suc q) dispatched

/-- The atom front retains a typed open bottom literal. The free test is
rejected physically on the tag, then the bottom test accepts. -/
theorem exact_OpenShiftHitAtomsBottom (V : Program 1) (H : Program 2) (t d : OTerm α)
    (typed : D B Γ (unary V (suc z) (bottomTerm t))) :
    D B Γ (programGraph (shiftHitAtoms V H) (suc (bottomTerm t)) ![bottomTerm t,d]) := by
  let q := bottomTerm t
  let xs : Fin 3 → OTerm α := ![q,d,q]
  let U := shiftHitFallback H
  have valid : D B Γ (bit (singletonSyntax V) xs) := exact_OpenSingletonSyntax V q d q typed typed
  have literalTag : D B Γ (unary (literal 1 3) (numeral 3) q) := literalGraph 3 ![q]
  have shape : D B Γ (unary bottomTest (suc z) q) :=
    (packedNode (literal 1 3) (numeral 3) [t] literalTag).1
  have isBottom : D B Γ (bit (onRaw bottomTest 2) xs) := onTape bottomTest 2 (suc z) xs shape
  have notFree : D B Γ (programGraph (onRaw freeTest 2) z xs) :=
    onTape freeTest 2 z xs (exact_OpenLiteralOtherTag 0 3 2 [t] (by decide))
  have inner : D B Γ (programGraph (branch (onRaw bottomTest 2) U retainSingleton) (suc q) xs) :=
    successorBranchIntro (onRaw bottomTest 2) U retainSingleton (suc q) z xs isBottom
      (exact_OpenSingletonRetain q d q)
  have dispatch : D B Γ (programGraph (singletonAtomicDispatch U) (suc q) xs) :=
    zeroBranchIntro (onRaw freeTest 2) (branch (onRaw bottomTest 2) U retainSingleton)
      retainSingleton (suc q) xs notFree inner
  have dispatched : D B Γ (programGraph (shiftAtomDispatch V H) (suc q) xs) :=
    successorBranchIntro (singletonSyntax V) U (singletonAtomicDispatch U) (suc q) z xs
      valid dispatch
  exact exact_OpenReplacementTape (shiftAtomDispatch V H) q d (suc q) dispatched

/-- The atom front passes a guarded non-atom replacement to `H`. -/
theorem exact_OpenShiftHitAtomsPass (V : Program 1) (H : Program 2) (a d out : OTerm α)
    (typed : D B Γ (unary V (suc z) a))
    (notFree : D B Γ (unary freeTest z a)) (notBottom : D B Γ (unary bottomTest z a))
    (h : D B Γ (programGraph H out ![a,d])) :
    D B Γ (programGraph (shiftHitAtoms V H) out ![a,d]) := by
  let xs : Fin 3 → OTerm α := ![a,d,a]
  let U := shiftHitFallback H
  have valid : D B Γ (bit (singletonSyntax V) xs) := exact_OpenSingletonSyntax V a d a typed typed
  have passed : D B Γ (programGraph U out xs) := exact_OpenShiftHitFallback H a d a out h
  have inner : D B Γ (programGraph (branch (onRaw bottomTest 2) U retainSingleton) out xs) :=
    zeroBranchIntro (onRaw bottomTest 2) U retainSingleton out xs
      (onTape bottomTest 2 z xs notBottom) passed
  have dispatch : D B Γ (programGraph (singletonAtomicDispatch U) out xs) :=
    zeroBranchIntro (onRaw freeTest 2) (branch (onRaw bottomTest 2) U retainSingleton)
      retainSingleton out xs (onTape freeTest 2 z xs notFree) inner
  have dispatched : D B Γ (programGraph (shiftAtomDispatch V H) out xs) :=
    successorBranchIntro (singletonSyntax V) U (singletonAtomicDispatch U) out z xs valid dispatch
  exact exact_OpenReplacementTape (shiftAtomDispatch V H) a d out dispatched

/-- Unified front on a free literal: the bound test is rejected on the
tag, then the atom front retains. -/
theorem exact_OpenShiftHitLiteralsFree (V : Program 1) (H : Program 2) (t n d : OTerm α)
    (typed : D B Γ (unary V (suc z) (freeTerm t n))) :
    D B Γ (programGraph (shiftHitLiterals V H) (suc (freeTerm t n)) ![freeTerm t n,d]) := by
  have notBound : D B Γ (unary boundShape z (freeTerm t n)) :=
    exact_OpenLiteralOtherTag 1 0 2 [t,n] (by decide)
  exact exact_OpenShiftHitBoundPass V (shiftHitAtoms V H) (freeTerm t n) d (suc (freeTerm t n))
    typed notBound (exact_OpenShiftHitAtomsFree V H t n d typed)

theorem exact_OpenShiftHitLiteralsBottom (V : Program 1) (H : Program 2) (t d : OTerm α)
    (typed : D B Γ (unary V (suc z) (bottomTerm t))) :
    D B Γ (programGraph (shiftHitLiterals V H) (suc (bottomTerm t)) ![bottomTerm t,d]) := by
  have notBound : D B Γ (unary boundShape z (bottomTerm t)) :=
    exact_OpenLiteralOtherTag 1 3 2 [t] (by decide)
  exact exact_OpenShiftHitBoundPass V (shiftHitAtoms V H) (bottomTerm t) d (suc (bottomTerm t))
    typed notBound (exact_OpenShiftHitAtomsBottom V H t d typed)

/-- Regression: the bound-literal row of the unified front is the saved
theorem at the atom front as fallback. -/
theorem exact_OpenShiftHitLiteralsBound (V : Program 1) (H : Program 2) (ty i d : OTerm α)
    (typed : D B Γ (unary V (suc z) (boundTerm ty i))) :
    D B Γ (programGraph (shiftHitLiterals V H) (suc (boundTerm ty (add i d)))
      ![boundTerm ty i,d]) :=
  exact_OpenShiftHitBound V (shiftHitAtoms V H) ty i d typed

/-- The retained dependency, stated as a premise: on a guarded packed
node whose tag is none of 0, 1, 3 the unified front returns exactly what
an actual open graph of the supplied `H` returns. For the recursive tags
that graph must come from the course-of-values shift table; nothing here
supplies it. -/
theorem exact_OpenShiftHitLiteralsOtherTag (V : Program 1) (H : Program 2)
    (tag : Nat) (payload : List (OTerm α)) (d out : OTerm α)
    (notFree : tag ≠ 0) (notBound : tag ≠ 1) (notBottom : tag ≠ 3)
    (typed : D B Γ (unary V (suc z) (rawCons (numeral tag) (packedBody payload))))
    (computed : D B Γ (programGraph H out ![rawCons (numeral tag) (packedBody payload),d])) :
    D B Γ (programGraph (shiftHitLiterals V H) out
      ![rawCons (numeral tag) (packedBody payload),d]) := by
  let q := rawCons (numeral tag) (packedBody payload)
  have freeOff : D B Γ (unary freeTest z q) := exact_OpenLiteralOtherTag 0 tag 2 payload notFree
  have bottomOff : D B Γ (unary bottomTest z q) :=
    exact_OpenLiteralOtherTag 3 tag 1 payload notBottom
  have boundOff : D B Γ (unary boundShape z q) := exact_OpenLiteralOtherTag 1 tag 2 payload notBound
  exact exact_OpenShiftHitBoundPass V (shiftHitAtoms V H) q d out typed boundOff
    (exact_OpenShiftHitAtomsPass V H q d out typed freeOff bottomOff computed)

/-- Positive-depth equal-index row for a free literal replacement, with
no `H` graph premise. Type, name, depth and the node's type field are
symbolic; both syntax premises are retained. -/
theorem exact_OpenSingletonBoundShiftedFreeLiteral (V : Program 1) (H : Program 2)
    (U : Program 3) (ty n d t : OTerm α)
    (inserted : D B Γ (unary V (suc z) (freeTerm ty n)))
    (typedNode : D B Γ (unary V (suc z) (boundTerm t (suc d)))) :
    D B Γ (programGraph (singletonBound V (shiftHitLiterals V H) U) (suc (freeTerm ty n))
      ![freeTerm ty n,suc d,boundTerm t (suc d)]) :=
  exact_OpenSingletonBoundAtPositiveDepth V (shiftHitLiterals V H) U (freeTerm ty n) d t
    (suc (freeTerm ty n)) inserted typedNode
    (exact_OpenShiftHitLiteralsFree V H ty n (suc d) inserted)

theorem exact_OpenSingletonBoundShiftedBottomLiteral (V : Program 1) (H : Program 2)
    (U : Program 3) (ty d t : OTerm α)
    (inserted : D B Γ (unary V (suc z) (bottomTerm ty)))
    (typedNode : D B Γ (unary V (suc z) (boundTerm t (suc d)))) :
    D B Γ (programGraph (singletonBound V (shiftHitLiterals V H) U) (suc (bottomTerm ty))
      ![bottomTerm ty,suc d,boundTerm t (suc d)]) :=
  exact_OpenSingletonBoundAtPositiveDepth V (shiftHitLiterals V H) U (bottomTerm ty) d t
    (suc (bottomTerm ty)) inserted typedNode
    (exact_OpenShiftHitLiteralsBottom V H ty (suc d) inserted)

/-- Regression: the saved bound-literal hit on the unified front. -/
theorem exact_OpenSingletonBoundShiftedBoundLiteralUnified (V : Program 1) (H : Program 2)
    (U : Program 3) (ty i d t : OTerm α)
    (inserted : D B Γ (unary V (suc z) (boundTerm ty i)))
    (typedNode : D B Γ (unary V (suc z) (boundTerm t (suc d)))) :
    D B Γ (programGraph (singletonBound V (shiftHitLiterals V H) U)
      (suc (boundTerm ty (add i (suc d))))
      ![boundTerm ty i,suc d,boundTerm t (suc d)]) :=
  exact_OpenSingletonBoundShiftedBoundLiteral V (shiftHitAtoms V H) U ty i d t inserted typedNode

#print axioms exact_OpenReplacementTape
#print axioms exact_OpenShiftHitFallback
#print axioms exact_OpenShiftHitBoundPass
#print axioms exact_OpenShiftHitAtomsFree
#print axioms exact_OpenShiftHitAtomsBottom
#print axioms exact_OpenShiftHitAtomsPass
#print axioms exact_OpenShiftHitLiteralsFree
#print axioms exact_OpenShiftHitLiteralsBottom
#print axioms exact_OpenShiftHitLiteralsBound
#print axioms exact_OpenShiftHitLiteralsOtherTag
#print axioms exact_OpenSingletonBoundShiftedFreeLiteral
#print axioms exact_OpenSingletonBoundShiftedBottomLiteral
#print axioms exact_OpenSingletonBoundShiftedBoundLiteralUnified
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitAtomsOpenProof
