module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowDirectAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelopeTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalControlGraph (equal)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalSparsePathEnvelope
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserTargets (decodeResult)
open NumberedWindowDirectAlgorithm (Entry Witness)
open NumberedWindowFieldAlgorithm (unpackNode)
open SourceComputabilityFormulaSupportProof (numeral)

def guardAt (tag : Nat) : Program 1 := nodeGood (literal 1 tag) 3

def rawTriple (tag n : Nat) : Option (Nat × Nat × Nat) :=
  if run (guardAt tag) n = 1 then some (run (field 0) n,run (field 1) n,run (field 2) n) else none

def selectedList (n : Nat) : Option (List Nat) := decodeResult (run parser n)

def selectedEntries : List Nat → Option (List Entry)
  | [] => some []
  | n::ns => do
    let e ← rawTriple 4 n
    let es ← selectedEntries ns
    pure (e :: es)

/-- Literal tag-5 witness order is kept, removed, inserted.
Each tag-4 entry retains target, dominator, supplied certificate order. -/
def selectedWitness (n : Nat) : Option Witness := do
  let (k,r,a) ← rawTriple 5 n
  let kept ← selectedList k
  let removed ← selectedList r
  let raw ← selectedList a
  let added ← selectedEntries raw
  pure (kept,removed,added)

def ExactRawTriple : Prop := ∀ tag n,
  rawTriple tag n = (match unpackNode n with
    | some (actual,[a,b,c]) => if actual = tag then some (a,b,c) else none
    | _ => none)

def ExactSelectedWitness : Prop := ∀ n, selectedWitness n = NumberedWindowDirectAlgorithm.readWitness n

def tripleTerm {α : Type} (tag : Nat) (a b c : OrdinaryArithmetic.Term α) : OrdinaryArithmetic.Term α :=
  rawCons (numeral tag) (packedBody [a,b,c])

def reports {α : Type} (tag : Nat) (w a b c : OrdinaryArithmetic.Term α) : Formula α :=
  unary (guardAt tag) (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) w ⊓
    (unary (field 0) a w ⊓ (unary (field 1) b w ⊓ unary (field 2) c w))

/-- Actual open arithmetic equality reflects the same selected guard
and the three same raw field graph reports, in their literal order.
It does not say that an arbitrary original direct checker parses this tape. -/
def ExactOpenTriple : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (tag : Nat) (w a b c : OrdinaryArithmetic.Term α),
    let e := equal w (tripleTerm tag a b c)
    let g := reports tag w a b c
    Nonempty (Derivation B Γ ((e.imp g) ⊓ (g.imp e)))

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelopeTargets
