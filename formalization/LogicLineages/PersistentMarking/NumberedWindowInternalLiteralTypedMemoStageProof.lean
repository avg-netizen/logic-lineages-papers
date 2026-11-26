module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedDualMemoProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedContextUpdateProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoStageProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue outputTransport)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue oneConstantValue)
open ID1Completion.InternalEqualityTest (subtract)
open ID1Completion.InternalRawListRecursion (lookup)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons)
open NumberedWindowInternalSparsePair (pair pairTerm fieldCons)
open NumberedWindowInternalSparsePairGraphProof (consGraph)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalAuxExchangeMemoStepTargets
  (binaryAfter unaryAfter currentKey packedKey rawSource rawTarget)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (binaryGraph unaryGraph)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralTypedAuxEdgeGuardProof (readSlot typedAuxEdgeGuard)
open NumberedWindowInternalLiteralTypedContextUpdateProof (contextUpdate)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def carrierTerm {α : Type} (ctx old prev : OTerm α) : OTerm α :=
  rawCons ctx (rawCons old (rawCons prev z))

def memoCarrier : Program 4 :=
  consOf (.projection 2) (consOf (.projection 1) (consOf (.projection 0) (constantZero 4)))

def after1 (p q : Program 1) : Program 1 := .composition p (fun _ : Fin 1 => q)
def holdContext : Program 1 := cellHead
def holdTable : Program 1 := after1 cellHead cellTail
def holdIndex : Program 1 := after1 cellHead (after1 cellTail cellTail)

def baseOnCarrier (Base : Program 4) : Program 4 :=
  .composition Base ![readSlot holdContext 0,.projection 1,.projection 2,.projection 3]

def lookupOnCarrier (i j : Fin 4) : Program 4 :=
  let key := binaryAfter pair (.projection i) (.projection j)
  let lag := binaryAfter subtract key (readSlot holdIndex 0)
  binaryAfter lookup lag (readSlot holdTable 0)

def childOnCarrier (Base : Program 4) : Program 4 :=
  conjunction (baseOnCarrier Base) (conjunction (lookupOnCarrier 2 3) (lookupOnCarrier 3 2))

def stageGuard (Base : Program 4) : Program 4 :=
  typedAuxEdgeGuard (constantOne 4) (childOnCarrier Base)

/-- There is no recursive Program-valued definition. The stage reads
both earlier row positions from its numeric table parameter. The typed
edge checker remains a separate literal input, called at each extracted
child's own type without shifting the lexical environment. -/
def typedMemoStage (Base : Program 4) : Program 4 :=
  .composition (stageGuard Base) ![memoCarrier,constantZero 4,rawSource,rawTarget]

private theorem carrierValue (ctx old prev : OTerm α) :
    D B Γ (programGraph memoCarrier (carrierTerm ctx old prev) ![prev,old,ctx,z]) := by
  let xs : Fin 4 → OTerm α := ![prev,old,ctx,z]
  let a := rawCons prev z
  let b := rawCons old a
  have first : D B Γ (programGraph (consOf (.projection 0) (constantZero 4)) a xs) :=
    binaryGraph fieldCons (.projection 0) (constantZero 4) a prev z xs
      (consGraph prev z) (projectionValue 0 xs) (zeroConstantValue xs)
  have second : D B Γ (programGraph
      (consOf (.projection 1) (consOf (.projection 0) (constantZero 4))) b xs) :=
    binaryGraph fieldCons (.projection 1) _ b old a xs (consGraph old a) (projectionValue 1 xs) first
  exact binaryGraph fieldCons (.projection 2) _ (carrierTerm ctx old prev) ctx b xs
    (consGraph ctx b) (projectionValue 2 xs) second

/-- The actual memo update is the typed structural guard on the decoded
parent raw pair. The retaping proof works under arbitrary object hypotheses. -/
theorem exact_OpenTypedMemoStage (Base : Program 4) (ctx old prev q r : OTerm α)
    (parent : D B Γ (eqn (suc prev) (pairTerm q r))) :
    D B Γ (contextUpdate (typedMemoStage Base) (suc z) ctx prev old) ↔
      D B Γ (acceptEdge (stageGuard Base) (carrierTerm ctx old prev) z q r) := by
  let xs : Fin 4 → OTerm α := ![prev,old,ctx,z]
  let ys : Fin 4 → OTerm α := ![carrierTerm ctx old prev,z,q,r]
  let ps : Fin 4 → Program 4 := ![memoCarrier,constantZero 4,rawSource,rawTarget]
  have first : D B Γ (programGraph currentKey (suc prev) xs) :=
    unaryGraph .succ (.projection 0) (suc prev) prev xs (successorValue ![prev]) (projectionValue 0 xs)
  have key := outputTransport currentKey (suc prev) (pairTerm q r) xs parent first
  have packed : D B Γ (programGraph packedKey (rawCons q r) xs) :=
    unaryGraph .succ currentKey (rawCons q r) (pairTerm q r) xs (successorValue ![pairTerm q r]) key
  obtain ⟨decoded⟩ := canonicalCell (body := B) (Γ := Γ) q r
  have a := unaryGraph cellHead packedKey q (rawCons q r) xs
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight decoded)⟩ packed
  have b := unaryGraph cellTail packedKey r (rawCons q r) xs
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight decoded)⟩ packed
  have tape : ∀ i, D B Γ (programGraph (ps i) (ys i) xs) := fun i =>
    Fin.cases (carrierValue ctx old prev) (Fin.cases (zeroConstantValue xs)
      (Fin.cases a (Fin.cases b (fun j => Fin.elim0 j)))) i
  constructor
  · intro h
    exact compositionRecover (stageGuard Base) ps (suc z) xs ys h tape
  · intro h
    exact compositionValue (stageGuard Base) ps (suc z) xs ys h tape

#print axioms exact_OpenTypedMemoStage
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoStageProof
