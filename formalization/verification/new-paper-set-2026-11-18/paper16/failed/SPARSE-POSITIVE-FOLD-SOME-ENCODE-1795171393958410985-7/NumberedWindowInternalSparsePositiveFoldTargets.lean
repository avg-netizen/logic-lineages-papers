module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFold
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodec (consCode)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseFieldInductionTargets (malformed consGraph)
open NumberedWindowInternalSparsePathAdvanceTargets
open NumberedWindowInternalSparsePositiveFold

def encodeScratch (cursor current : Nat) : Nat := 1 + Nat.pair cursor current

/-- The actual original ordered partial body parse followed by a left
fold, starting from the unchanged Option. Empty input retains the start
even if the context raw code is malformed: it has performed no hop. -/
def originalFold (entries : Entries) (s : Settings)
    (ctx ty current certificate : Nat) : Option Nat := do
  let hops ← unpack certificate
  hops.foldl (fun currentState hop => packedOriginalAdvance entries s ctx ty (encodeState currentState) hop)
    (decodeState current)

def packedPositive (entries : Entries) (s : Settings)
    (ctx ty source certificate target : Nat) : Bool :=
  (unpack ctx).any (fun g =>
    NumberedWindowPositivePathAlgorithm.positive (NumberedWindowConcreteCheckers.step entries s)
      (NumberedWindowScalarAlgorithm.least s) g ty source certificate target)

def ActualFuelCalibration (entries : Entries) (s : Settings) (raw : Program 5) (least : Program 3) : Prop :=
  ∀ ctx ty current certificate fuel, certificate ≤ fuel →
    evaluate (iterateState raw least) (fuel ::ᵥ ctx ::ᵥ ty ::ᵥ current ::ᵥ certificate ::ᵥ nil) =
      encodeScratch 0 (encodeState (originalFold entries s ctx ty current certificate))

def ActualPositiveCalibration (entries : Entries) (s : Settings)
    (raw : Program 5) (least : Program 3) : Prop :=
  ∀ ctx ty source certificate target,
    evaluate (positive raw least) (ctx ::ᵥ ty ::ᵥ source ::ᵥ certificate ::ᵥ target ::ᵥ nil) =
      if packedPositive entries s ctx ty source certificate target then 1 else 0

def FoldComposition : Prop :=
  ∀ (entries : Entries) (s : Settings) (raw : Program 5) (least : Program 3),
    ActualAdvanceCalibration entries s raw least →
      ActualFuelCalibration entries s raw least ∧ ActualPositiveCalibration entries s raw least

def ConcretePositive : Prop :=
  ∀ (entries : Entries) (s : Settings), ∃ (raw : Program 5) (least : Program 3),
    ActualRawCalibration entries s raw ∧ ActualLeastCalibration s least ∧
      ActualAdvanceCalibration entries s raw least ∧
      ActualFuelCalibration entries s raw least ∧ ActualPositiveCalibration entries s raw least

def scratchGraph {α : Type} (state cursor current : OTerm α) : Formula α :=
  programGraph consCode state ![cursor,current]

def stepGraph {α : Type} (raw : Program 5) (least : Program 3)
    (out counter prior ctx ty initial certificate : OTerm α) : Formula α :=
  programGraph (iterateStep raw least) out ![counter,prior,ctx,ty,initial,certificate]

def loopGraph {α : Type} (raw : Program 5) (least : Program 3)
    (out fuel ctx ty initial certificate : OTerm α) : Formula α :=
  programGraph (iterateState raw least) out ![fuel,ctx,ty,initial,certificate]

def OpenFoldBase : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3)
    (α : Type) (state ctx ty initial certificate : OTerm α),
    Nonempty (Derivation body [] ((scratchGraph state certificate initial).imp
      (loopGraph raw least state z ctx ty initial certificate)))

def OpenNilRetention : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3)
    (α : Type) (counter prior ctx ty initial certificate current : OTerm α),
    Nonempty (Derivation body [] ((scratchGraph prior z current).imp
      (stepGraph raw least prior counter prior ctx ty initial certificate)))

def OpenMalformedCollapse : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3)
    (α : Type) (out counter prior ctx ty initial certificate cursor current : OTerm α),
    let a := scratchGraph prior cursor current ⊓ (malformed cursor ⊓ scratchGraph out z z)
    Nonempty (Derivation body [] (a.imp (stepGraph raw least out counter prior ctx ty initial certificate)))

def OpenConsUpdate : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3)
    (α : Type) (out counter prior ctx ty initial certificate cursor current x xs next : OTerm α),
    let a := scratchGraph prior cursor current ⊓
      (consGraph cursor x xs ⊓ (selectedGraph raw least next ctx ty current x ⊓ scratchGraph out xs next))
    Nonempty (Derivation body [] (a.imp (stepGraph raw least out counter prior ctx ty initial certificate)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldTargets
