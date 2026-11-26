module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitAtomsOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBetaInstallationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonGuardedCalibrationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBetaTransportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitInstallationProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program evaluate)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowRootDispatchAlgorithm (fixed)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalLiteralRootDispatchNumericProof (LeafFit)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralAtomicRawShapeProof (freeTerm bottomTerm)
open NumberedWindowInternalLiteralBetaLeafProof (InstanceFit withBetaLeaf)
open NumberedWindowInternalLiteralBetaLeafNumericProof (exact_LiteralBetaLeafFit)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralSingletonDepthNumericProof
  (DepthInstanceFit zeroDepthInstance exact_ZeroDepthInstance)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (ShiftHitFit shiftHitValue singletonBound)
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof (boundTerm)
open NumberedWindowInternalLiteralSingletonBoundOpenHitProof (exact_OpenSingletonBoundAtPositiveDepth)
open NumberedWindowInternalLiteralSingletonBetaInstallationProof (exact_PhysicalSingletonBetaInstallation)
open NumberedWindowInternalLiteralSingletonGuardedCalibrationProof
  (GuardedDepthInstanceFit exact_LiteralSingletonBoundGuardedCalibration
    exact_LiteralSingletonLambdaCalibrationOfGuarded)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda singletonLambdaDispatch)
open NumberedWindowInternalLiteralSingletonLambdaOpenRowsProof (exact_OpenBetaLambdaBody)
open NumberedWindowInternalLiteralSingletonLambdaBetaTransportProof (exact_OpenBetaLambdaBodyTargetAt)
open NumberedWindowInternalLiteralSingletonShiftHitOpenProof (exact_OpenShiftHitNumeral)
open NumberedWindowInternalLiteralSingletonShiftHitAtomsMachineProof
  (shiftHitLiterals exact_ShiftHitLiteralsFit)
open NumberedWindowInternalLiteralSingletonShiftHitAtomsOpenProof
  (exact_OpenShiftHitLiteralsBound exact_OpenShiftHitLiteralsFree exact_OpenShiftHitLiteralsBottom)

/-- The existing beta installation at `H := shiftHitLiterals V H`: same
`V`, same all-input `U` premise, and the supplied `H` kept as the guarded
fallback of the literal front. -/
theorem exact_PhysicalSingletonBetaLiteralsInstallation (xs : Entries) (heads : List Nat)
    (V : Program 1) (H : Program 2) (U : Program 3) (leaf : Nat → Program 3)
    (vFit : ActualRawSyntax V) (hFit : ShiftHitFit H) (uFit : DepthInstanceFit U)
    (fit : LeafFit (fixed xs heads) leaf) :
    let betaInstance := zeroDepthInstance (singletonBound V (shiftHitLiterals V H) U)
    InstanceFit betaInstance ∧ LeafFit (fixed xs heads) (withBetaLeaf V betaInstance leaf) :=
  exact_PhysicalSingletonBetaInstallation xs heads V (shiftHitLiterals V H) U leaf vFit
    (exact_ShiftHitLiteralsFit V H vFit hFit) uFit fit

/-- Same installation with the slot calibrated only behind the syntax
guard, through the existing guarded bound calibration. -/
theorem exact_PhysicalSingletonBetaLiteralsGuardedInstallation (xs : Entries) (heads : List Nat)
    (V : Program 1) (H : Program 2) (U : Program 3) (leaf : Nat → Program 3)
    (vFit : ActualRawSyntax V) (hFit : ShiftHitFit H) (uFit : GuardedDepthInstanceFit U)
    (fit : LeafFit (fixed xs heads) leaf) :
    let betaInstance := zeroDepthInstance (singletonBound V (shiftHitLiterals V H) U)
    InstanceFit betaInstance ∧ LeafFit (fixed xs heads) (withBetaLeaf V betaInstance leaf) := by
  have instanceFit := exact_ZeroDepthInstance (singletonBound V (shiftHitLiterals V H) U)
    (exact_LiteralSingletonBoundGuardedCalibration V (shiftHitLiterals V H) U vFit
      (exact_ShiftHitLiteralsFit V H vFit hFit) uFit)
  exact ⟨instanceFit, exact_LiteralBetaLeafFit xs heads V _ vFit instanceFit leaf fit⟩

/-- The lambda program with the same installed shift. The guarded fit of
the written lambda dispatch stays an explicit premise; it is not proved
here. Taking `U := singletonBound V (shiftHitLiterals V H) U'` gives the
program of the scoped rows below. -/
theorem exact_PhysicalSingletonLambdaLiteralsInstallation (xs : Entries) (heads : List Nat)
    (V : Program 1) (H : Program 2) (U : Program 3) (leaf : Nat → Program 3)
    (vFit : ActualRawSyntax V) (hFit : ShiftHitFit H)
    (slotFit : GuardedDepthInstanceFit (singletonLambdaDispatch U))
    (fit : LeafFit (fixed xs heads) leaf) :
    let betaInstance := zeroDepthInstance (singletonLambda V (shiftHitLiterals V H) U)
    InstanceFit betaInstance ∧ LeafFit (fixed xs heads) (withBetaLeaf V betaInstance leaf) := by
  have instanceFit := exact_ZeroDepthInstance (singletonLambda V (shiftHitLiterals V H) U)
    (exact_LiteralSingletonLambdaCalibrationOfGuarded V (shiftHitLiterals V H) U vFit
      (exact_ShiftHitLiteralsFit V H vFit hFit) slotFit)
  exact ⟨instanceFit, exact_LiteralBetaLeafFit xs heads V _ vFit instanceFit leaf fit⟩

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Closed numeral property of the installed shift: at every numeral
replacement code and positive numeral depth its graph holds at the
original shift-hit value. This covers every tag, recursive ones
included, but only at numerals. -/
theorem exact_OpenInstalledShiftHitNumeral (V : Program 1) (H : Program 2)
    (vFit : ActualRawSyntax V) (hFit : ShiftHitFit H) (n k : Nat) :
    D B Γ (programGraph (shiftHitLiterals V H) (numeral (shiftHitValue n (k+1)))
      ![numeral n,suc (numeral k)]) := by
  have closed := exact_OpenShiftHitNumeral (B := B) (α := α) (Γ := Γ) (shiftHitLiterals V H) n k
  have value : evaluate (shiftHitLiterals V H)
      (List.Vector.cons n (List.Vector.cons (k+1) List.Vector.nil)) = shiftHitValue n (k+1) :=
    exact_ShiftHitLiteralsFit V H vFit hFit n (k+1)
  rw [value] at closed
  exact closed

/-- Bridge to the scoped beta consumer. Under one binder the discharged
index is `suc z`, so the child call of the lambda row is the
positive-depth equal-index row; a shift-hit graph with a
successor-shaped output is all the row needs. `U` is arbitrary; with
`U := singletonLambdaDispatch U'` the slot is `singletonLambda V H U'`. -/
theorem exact_OpenBetaLambdaBoundHit (V : Program 1) (H : Program 2) (U : Program 3)
    (a lamTy t b' : OTerm α)
    (inserted : D B Γ (unary V (suc z) a))
    (outerNode : D B Γ (unary V (suc z) (rawLambdaTerm lamTy (boundTerm t (suc z)))))
    (innerNode : D B Γ (unary V (suc z) (boundTerm t (suc z))))
    (hit : D B Γ (programGraph H (suc b') ![a,suc z])) :
    D B Γ (programGraph (zeroDepthInstance (singletonLambda V H (singletonBound V H U)))
      (suc (rawLambdaTerm lamTy b')) ![a,rawLambdaTerm lamTy (boundTerm t (suc z))]) :=
  exact_OpenBetaLambdaBody V H (singletonBound V H U) a lamTy (boundTerm t (suc z)) b'
    inserted outerNode
    (exact_OpenSingletonBoundAtPositiveDepth V H U a z t (suc b') inserted innerNode hit)

/-- The same bridge in the accepted-leaf form: the leaf's own instance
graph at an abstract body, derivably a lambda over the discharged index. -/
theorem exact_OpenBetaLambdaBoundHitTargetAt (V : Program 1) (H : Program 2) (U : Program 3)
    (a body lamTy t b' r : OTerm α)
    (inserted : D B Γ (unary V (suc z) a))
    (outerNode : D B Γ (unary V (suc z) (rawLambdaTerm lamTy (boundTerm t (suc z)))))
    (innerNode : D B Γ (unary V (suc z) (boundTerm t (suc z))))
    (shape : D B Γ (eqn body (rawLambdaTerm lamTy (boundTerm t (suc z)))))
    (hit : D B Γ (programGraph H (suc b') ![a,suc z]))
    (held : D B Γ (programGraph (zeroDepthInstance (singletonLambda V H (singletonBound V H U)))
      (suc r) ![a,body])) :
    D B Γ (eqn (suc r) (suc (rawLambdaTerm lamTy b'))) :=
  exact_OpenBetaLambdaBodyTargetAt V H (singletonBound V H U) a body lamTy (boundTerm t (suc z))
    b' r inserted outerNode shape
    (exact_OpenSingletonBoundAtPositiveDepth V H U a z t (suc b') inserted innerNode hit) held

/-- Installed, bound literal replacement: the index is raised by the
binder depth one. No graph premise on the shift program remains. -/
theorem exact_OpenBetaLambdaShiftedBoundLiteral (V : Program 1) (H : Program 2) (U : Program 3)
    (ty i lamTy t : OTerm α)
    (inserted : D B Γ (unary V (suc z) (boundTerm ty i)))
    (outerNode : D B Γ (unary V (suc z) (rawLambdaTerm lamTy (boundTerm t (suc z)))))
    (innerNode : D B Γ (unary V (suc z) (boundTerm t (suc z)))) :
    D B Γ (programGraph
      (zeroDepthInstance (singletonLambda V (shiftHitLiterals V H)
        (singletonBound V (shiftHitLiterals V H) U)))
      (suc (rawLambdaTerm lamTy (boundTerm ty (add i (suc z)))))
      ![boundTerm ty i,rawLambdaTerm lamTy (boundTerm t (suc z))]) :=
  exact_OpenBetaLambdaBoundHit V (shiftHitLiterals V H) U (boundTerm ty i) lamTy t
    (boundTerm ty (add i (suc z))) inserted outerNode innerNode
    (exact_OpenShiftHitLiteralsBound V H ty i (suc z) inserted)

theorem exact_OpenBetaLambdaShiftedFreeLiteral (V : Program 1) (H : Program 2) (U : Program 3)
    (ty n lamTy t : OTerm α)
    (inserted : D B Γ (unary V (suc z) (freeTerm ty n)))
    (outerNode : D B Γ (unary V (suc z) (rawLambdaTerm lamTy (boundTerm t (suc z)))))
    (innerNode : D B Γ (unary V (suc z) (boundTerm t (suc z)))) :
    D B Γ (programGraph
      (zeroDepthInstance (singletonLambda V (shiftHitLiterals V H)
        (singletonBound V (shiftHitLiterals V H) U)))
      (suc (rawLambdaTerm lamTy (freeTerm ty n)))
      ![freeTerm ty n,rawLambdaTerm lamTy (boundTerm t (suc z))]) :=
  exact_OpenBetaLambdaBoundHit V (shiftHitLiterals V H) U (freeTerm ty n) lamTy t
    (freeTerm ty n) inserted outerNode innerNode
    (exact_OpenShiftHitLiteralsFree V H ty n (suc z) inserted)

theorem exact_OpenBetaLambdaShiftedBottomLiteral (V : Program 1) (H : Program 2) (U : Program 3)
    (ty lamTy t : OTerm α)
    (inserted : D B Γ (unary V (suc z) (bottomTerm ty)))
    (outerNode : D B Γ (unary V (suc z) (rawLambdaTerm lamTy (boundTerm t (suc z)))))
    (innerNode : D B Γ (unary V (suc z) (boundTerm t (suc z)))) :
    D B Γ (programGraph
      (zeroDepthInstance (singletonLambda V (shiftHitLiterals V H)
        (singletonBound V (shiftHitLiterals V H) U)))
      (suc (rawLambdaTerm lamTy (bottomTerm ty)))
      ![bottomTerm ty,rawLambdaTerm lamTy (boundTerm t (suc z))]) :=
  exact_OpenBetaLambdaBoundHit V (shiftHitLiterals V H) U (bottomTerm ty) lamTy t
    (bottomTerm ty) inserted outerNode innerNode
    (exact_OpenShiftHitLiteralsBottom V H ty (suc z) inserted)

/-- Accepted-leaf form for the bound literal replacement. -/
theorem exact_OpenBetaLambdaShiftedBoundLiteralTargetAt (V : Program 1) (H : Program 2)
    (U : Program 3) (ty i body lamTy t r : OTerm α)
    (inserted : D B Γ (unary V (suc z) (boundTerm ty i)))
    (outerNode : D B Γ (unary V (suc z) (rawLambdaTerm lamTy (boundTerm t (suc z)))))
    (innerNode : D B Γ (unary V (suc z) (boundTerm t (suc z))))
    (shape : D B Γ (eqn body (rawLambdaTerm lamTy (boundTerm t (suc z)))))
    (held : D B Γ (programGraph
      (zeroDepthInstance (singletonLambda V (shiftHitLiterals V H)
        (singletonBound V (shiftHitLiterals V H) U)))
      (suc r) ![boundTerm ty i,body])) :
    D B Γ (eqn (suc r) (suc (rawLambdaTerm lamTy (boundTerm ty (add i (suc z)))))) :=
  exact_OpenBetaLambdaBoundHitTargetAt V (shiftHitLiterals V H) U (boundTerm ty i) body lamTy t
    (boundTerm ty (add i (suc z))) r inserted outerNode innerNode shape
    (exact_OpenShiftHitLiteralsBound V H ty i (suc z) inserted) held

#print axioms exact_PhysicalSingletonBetaLiteralsInstallation
#print axioms exact_PhysicalSingletonBetaLiteralsGuardedInstallation
#print axioms exact_PhysicalSingletonLambdaLiteralsInstallation
#print axioms exact_OpenInstalledShiftHitNumeral
#print axioms exact_OpenBetaLambdaBoundHit
#print axioms exact_OpenBetaLambdaBoundHitTargetAt
#print axioms exact_OpenBetaLambdaShiftedBoundLiteral
#print axioms exact_OpenBetaLambdaShiftedFreeLiteral
#print axioms exact_OpenBetaLambdaShiftedBottomLiteral
#print axioms exact_OpenBetaLambdaShiftedBoundLiteralTargetAt
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonShiftHitInstallationProof
