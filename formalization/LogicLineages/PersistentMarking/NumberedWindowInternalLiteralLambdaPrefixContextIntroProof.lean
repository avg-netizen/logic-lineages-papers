module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixParentStopProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaFrameOpenPartsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaOpenRowsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixContextIntroProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue headTransport projectionValue)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual equalitySelf)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw frameSlot sameSlot)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (consOfGraph)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralBetaLeafProof (rawLambdaShape)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralSingletonLambdaOpenRowsProof (exact_OpenLambdaRead)
open NumberedWindowInternalLiteralLambdaFrameProof (lambdaFrameGuard)
open NumberedWindowInternalLiteralLambdaFrameOpenPartsProof (LambdaParts)
open NumberedWindowInternalLiteralLambdaLexicalGateProof
open NumberedWindowInternalLiteralLambdaPrefixMachineProof
open NumberedWindowInternalLiteralLambdaPrefixLiveOpenProof (bit5 exact_OpenPrefixTest exact_OpenPrefixLifts)
open NumberedWindowInternalLiteralLambdaPrefixParentStopProof (exact_OpenContextualLambdaPrefixAfterStop)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The actual frame and lexical reports construct the first contextual
tick of the prefix checker at the very same window. -/
theorem exact_OpenContextualLambdaPrefixTick (W : Program 3)
    (c t q w r d a inner e b cod : OTerm α)
    (header : D B Γ (unary cellHead (numeral 2) q))
    (row : LambdaParts B Γ q w r d a inner e b)
    (arrow : D B Γ (eqn t (rawCons d cod)))
    (left : D B Γ (windowAt W (rawCons d c) cod a))
    (right : D B Γ (windowAt W (rawCons d c) cod b)) :
    D B Γ (programGraph (prefixTick W) (prefixStartTerm (rawCons d c) cod a inner b)
      ![prefixStartTerm c t q w r]) := by
  let xs : Fin 3 → OTerm α := ![q,w,r]
  let tape : Fin 5 → OTerm α := ![c,t,q,w,r]
  obtain ⟨qShape,qType,qBody⟩ := exact_OpenLambdaRead (B := B) (Γ := Γ) d a
  obtain ⟨rShape,rType,rBody⟩ := exact_OpenLambdaRead (B := B) (Γ := Γ) e b
  have readBinder := headTransport (field 0) d (rawLambdaTerm d a) q Fin.elim0 (row.source.map symm) qType
  have readOther := headTransport (field 0) e (rawLambdaTerm e b) r Fin.elim0 (row.target.map symm) rType
  have readSource := headTransport (field 1) a (rawLambdaTerm d a) q Fin.elim0 (row.source.map symm) qBody
  have readTarget := headTransport (field 1) b (rawLambdaTerm e b) r Fin.elim0 (row.target.map symm) rBody
  have sourceShape := headTransport rawLambdaShape (suc z) (rawLambdaTerm d a) q
    Fin.elim0 (row.source.map symm) qShape
  have targetShape := headTransport rawLambdaShape (suc z) (rawLambdaTerm e b) r
    Fin.elim0 (row.target.map symm) rShape
  have same : D B Γ (bit (sameSlot 0) xs) := by
    apply compositionValue equalityTest ![frameSlot 0 0,frameSlot 0 2] (suc z) xs ![d,e]
      (equalityOfEqual d e row.binder)
    intro i
    exact Fin.cases (onTape (field 0) 0 d xs readBinder)
      (Fin.cases (onTape (field 0) 2 e xs readOther) (fun j => Fin.elim0 j)) i
  have frame : D B Γ (bit lambdaFrameGuard xs) :=
    conjunctionAccept _ _ xs (onTape rawLambdaShape 0 (suc z) xs sourceShape)
      (conjunctionAccept _ _ xs (onTape rawLambdaShape 2 (suc z) xs targetShape) same)
  have liftedFrame : D B Γ (bit5 (rawTripleCall lambdaFrameGuard) tape) := by
    apply compositionValue lambdaFrameGuard ![.projection 2,.projection 3,.projection 4]
      (suc z) tape xs frame
    intro i
    exact Fin.cases (projectionValue 2 tape) (Fin.cases (projectionValue 3 tape)
      (Fin.cases (projectionValue 4 tape) (fun j => Fin.elim0 j))) i
  have readWitness : D B Γ (unary (field 0) inner w) := by
    apply compositionRecover (field 0) (fun _ : Fin 1 => .projection (1 : Fin 3)) inner xs ![w] row.childSlot
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 xs
  let arrowCode := rawCons d cod
  obtain ⟨cell⟩ := canonicalCell (body := B) (Γ := Γ) d cod
  have good := headTransport cellGood (suc z) arrowCode t Fin.elim0 (arrow.map symm)
    ⟨Derivation.conjunctionLeft cell⟩
  have domain := headTransport cellHead d arrowCode t Fin.elim0 (arrow.map symm)
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩
  have residue := headTransport cellTail cod arrowCode t Fin.elim0 (arrow.map symm)
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight cell)⟩
  have binderAt : D B Γ (programGraph lexicalBinder d tape) := lexicalSlotAt (field 0) 2 d tape readBinder
  have domAt : D B Γ (programGraph lexicalDomain d tape) := lexicalSlotAt cellHead 1 d tape domain
  have codAt : D B Γ (programGraph lexicalCodomain cod tape) := lexicalSlotAt cellTail 1 cod tape residue
  have agrees : D B Γ (bit5 (.composition equalityTest ![lexicalDomain,lexicalBinder]) tape) := by
    apply compositionValue equalityTest ![lexicalDomain,lexicalBinder] (suc z) tape ![d,d] (equalitySelf d)
    intro i
    exact Fin.cases domAt (Fin.cases binderAt (fun j => Fin.elim0 j)) i
  have arrowCheck : D B Γ (bit5 lexicalArrow tape) :=
    conjunctionAccept _ _ tape (lexicalSlotAt cellGood 1 (suc z) tape good) agrees
  have pushed : D B Γ (programGraph lexicalContext (rawCons d c) tape) :=
    consOfGraph lexicalBinder (.projection 0) d c tape binderAt (projectionValue 0 tape)
  have child (p : Program 5) (x : OTerm α) (view : D B Γ (programGraph p x tape))
      (win : D B Γ (windowAt W (rawCons d c) cod x)) : D B Γ (bit5 (lexicalWindowAt W p) tape) := by
    apply compositionValue W ![lexicalContext,lexicalCodomain,p] (suc z) tape ![rawCons d c,cod,x] win
    intro i
    exact Fin.cases pushed (Fin.cases codAt (Fin.cases view (fun j => Fin.elim0 j))) i
  have leftCheck := child lexicalSourceBody a (lexicalSlotAt (field 1) 2 a tape readSource) left
  have rightCheck := child lexicalTargetBody b (lexicalSlotAt (field 1) 4 b tape readTarget) right
  have lexical : D B Γ (bit5 (lambdaLexicalGate W) tape) :=
    conjunctionAccept _ _ tape arrowCheck (conjunctionAccept _ _ tape leftCheck rightCheck)
  have validated : D B Γ (bit5 (prefixValidation W) tape) := conjunctionAccept _ _ tape liftedFrame lexical
  exact exact_OpenPrefixLifts W c t q w r d cod a inner b
    (exact_OpenPrefixTest c t q w r d a inner e b header row) validated
    readBinder residue readSource readWitness readTarget

/-- A genuine contextual frame and the two actual pushed window reports
certify the parent if the same prefix evaluator stops at the child. -/
theorem exact_OpenContextualLambdaPrefixAtStoppedChild (W : Program 3)
    (c t q w r d a inner e b cod : OTerm α)
    (header : D B Γ (unary cellHead (numeral 2) q))
    (row : LambdaParts B Γ q w r d a inner e b)
    (arrow : D B Γ (eqn t (rawCons d cod)))
    (left : D B Γ (windowAt W (rawCons d c) cod a))
    (right : D B Γ (windowAt W (rawCons d c) cod b))
    (stopped : D B Γ (programGraph isLambdaPrefix z ![rawCons d c,cod,a,inner,b])) :
    D B Γ (bit5 (prefixOwn W) ![c,t,q,w,r]) :=
  exact_OpenContextualLambdaPrefixAfterStop W c t q w r (rawCons d c) cod a inner b
    (pairTerm (numeral 1) (packedBody [inner])) row.witness
    (exact_OpenContextualLambdaPrefixTick W c t q w r d a inner e b cod header row arrow left right) stopped

#print axioms exact_OpenContextualLambdaPrefixTick
#print axioms exact_OpenContextualLambdaPrefixAtStoppedChild
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixContextIntroProof
