module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch conjunction constantZero)
open InternalEqualityTest (subtract)
open InternalLessThan (constantOne ltTest)
open InternalRawListRecursion (lookup)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePair (pair)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparseRawFunctionFrame (frameGood frameSlot)
open NumberedWindowInternalAuxExchangeMemoTargets (StepCalibrated selected)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowFieldAlgorithm (packNode)

/-- All raw input numerals are allowed, and the chosen graph reports exactly the term bit. -/
def TermSyntaxCalibrated (V : Program 1) : Prop := ∀ n, run V n = (syntaxBits n).1.toNat

def unaryAfter (p : Program 1) (q : Program 4) : Program 4 :=
  .composition p (fun _ : Fin 1 => q)

def binaryAfter (p : Program 2) (q r : Program 4) : Program 4 :=
  .composition p (Fin.cons q (Fin.cons r Fin.elim0))

def currentKey : Program 4 := unaryAfter .succ (.projection 0)
def packedKey : Program 4 := unaryAfter .succ currentKey

def rawSource : Program 4 := unaryAfter cellHead packedKey
def rawTarget : Program 4 := unaryAfter cellTail packedKey

def goodKey : Program 4 := conjunction (unaryAfter cellGood packedKey) (constantOne 4)

/-- An auxiliary witness with a literal zero child is used only to reuse
the actual raw frame parser. It is not a reduction witness premise. -/
def dummyWitnessCode : Nat := packNode 5 [0]

def atFrame (p : Program 3) : Program 4 :=
  .composition p (Fin.cons rawSource (Fin.cons (literal 4 dummyWitnessCode) (Fin.cons rawTarget Fin.elim0)))

def childKey : Program 4 := binaryAfter pair (atFrame (frameSlot 2 0)) (atFrame (frameSlot 2 2))
def childEarlier : Program 4 := binaryAfter ltTest childKey currentKey
def childLag : Program 4 := binaryAfter subtract childKey (.projection 0)
def childResult : Program 4 := binaryAfter lookup childLag (.projection 1)

def enough (V : Program 1) : Program 4 :=
  conjunction (atFrame frameGood)
    (conjunction (unaryAfter V rawSource)
      (conjunction (unaryAfter V rawTarget) (conjunction childEarlier childResult)))

/-- An actual fold step on [predecessor key, previous table, 0, 0]. -/
def step (base : Program 2) (V : Program 1) : Program 4 :=
  branch goodKey (constantZero 4)
    (branch (enough V) (binaryAfter base rawSource rawTarget) (constantOne 4))

def ExactPhysicalAuxMemoStep : Prop :=
  ∀ (base : Program 2) (V : Program 1), TermSyntaxCalibrated V → StepCalibrated base (step base V)

def ExactPhysicalAuxMemoExchange : Prop :=
  ∀ (s : Settings) (base : Program 2) (V : Program 1),
    ActualTermExchange s base → TermSyntaxCalibrated V → ActualTermExchange s (selected (step base V))

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepTargets
