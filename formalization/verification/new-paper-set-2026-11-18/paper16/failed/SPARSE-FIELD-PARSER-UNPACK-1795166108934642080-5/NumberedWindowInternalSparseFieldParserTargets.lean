module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParser
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldInductionTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric (numbersNumber decodeNumbers)
open NumberedWindowFieldAlgorithm (unpack finish steps)
open NumberedWindowInternalSparseFieldCell (chosenCell)
open NumberedWindowInternalSparseFieldInductionTargets (malformed consGraph)
open NumberedWindowInternalSparseFieldParser

def encodeResult (result : Option (List Nat)) : Nat :=
  match result with
  | none => 0
  | some xs => numbersNumber xs + 1

def decodeResult : Nat → Option (List Nat)
  | 0 => none
  | k+1 => decodeNumbers k

/-- Typed only as scratch data. Every literal ordered list, including
duplicate fields, survives the scratch-code bridge. -/
def ScratchBridge : Prop := ∀ xs, decodeResult (encodeResult (some xs)) = some xs

/-- Full original bounded loop with an arbitrary prior accumulator and any
sufficient fuel. It never silently reverses or drops retained occurrences. -/
def BoundedOriginalFuelAccumulator : Prop :=
  ∀ (n fuel : Nat) (acc : List Nat), n ≤ fuel →
    finish (steps fuel (some (n,acc))) = (unpack n).map (fun xs => acc.reverse ++ xs)

def OriginalUnpackCases : Prop :=
  unpack 0 = some [] ∧
  (∀ n, chosenCell (n+1) = none → unpack (n+1) = none) ∧
  (∀ h t, unpack (NumberedWindowPairAlgorithm.pair h t + 1) =
    (unpack t).map (fun xs => h :: xs))

/-- Exact numerical Option representation of the entire decoded ordered
list for every raw source code, including failures anywhere in the tail. -/
def ActualEncodedOutput : Prop :=
  ∀ n, evaluate parser (n ::ᵥ nil) = encodeResult (unpack n)

def ActualDecodedOutput : Prop :=
  ∀ n, decodeResult (evaluate parser (n ::ᵥ nil)) = unpack n

def parserGraph {α : Type} (out n : OTerm α) : Formula α :=
  programGraph parser out ![n]

def OpenNilRow : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type),
    let n : OTerm α := OrdinaryArithmetic.zeroTerm
    Nonempty (Derivation body [] (parserGraph (OrdinaryArithmetic.succTerm n) n))

def OpenMalformedRow : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n : OTerm α),
    Nonempty (Derivation body [] ((malformed n).imp (parserGraph OrdinaryArithmetic.zeroTerm n)))

/-- A genuine raw cons uses the actual selected arithmetic output of its
smaller raw tail and the literal prepend program, not an assumed decoded list. -/
def OpenConsRow : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n h t out tailResult : OTerm α),
    let selected := parserGraph out n
    let row := programGraph prependResult out ![h,tailResult]
    Nonempty (Derivation body [] ((consGraph n h t ⊓ parserGraph tailResult t).imp
      ((selected.imp row) ⊓ (row.imp selected))))

def OpenRejectedTail : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n h t : OTerm α),
    let z : OTerm α := OrdinaryArithmetic.zeroTerm
    Nonempty (Derivation body [] ((consGraph n h t ⊓ parserGraph z t).imp (parserGraph z n)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTargets
