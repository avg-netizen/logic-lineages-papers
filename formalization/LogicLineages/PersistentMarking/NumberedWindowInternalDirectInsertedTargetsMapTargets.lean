module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelopeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsMapTargets
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open ID1Completion.InternalRawListRecursion (listRec)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalRawListRecursionTargets
open NumberedWindowInternalDirectWitnessEnvelopeTargets (guardAt)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserTargets (encodeResult)
open NumberedWindowInternalFreshProbeDispatchProgram (bothOne chooseBranch literal zeroAt predOne)
open NumberedWindowDirectAlgorithm (entries)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedMultisetNumeric (numbersNumber)

def targetBase : Program 0 := literal 0 1

def atHead (p : Program 1) : Program 2 := .composition p (Fin.cons (.projection 0) Fin.elim0)

def tailPayload : Program 2 := .composition predOne (Fin.cons (.projection 1) Fin.elim0)

def joined : Program 2 :=
  .composition consCode (Fin.cons (atHead (field 0)) (Fin.cons tailPayload Fin.elim0))

def targetStep : Program 2 :=
  chooseBranch (bothOne (atHead (guardAt 4)) (literal 2 1)) (zeroAt 2)
    (chooseBranch (.projection 1) (zeroAt 2) (.composition .succ (Fin.cons joined Fin.elim0)))

def scratchTargets : Program 1 := listRec targetBase targetStep

def parserPayload : Program 1 := .composition predOne (Fin.cons parser Fin.elim0)

def insertedTargets : Program 1 :=
  chooseBranch parser (zeroAt 1) (.composition scratchTargets (Fin.cons parserPayload Fin.elim0))

def mapped (rows : List Nat) : Option (List Nat) := (entries rows).map (List.map Prod.fst)

def ExactScratchTargets : Prop :=
  ∀ rows, evaluate scratchTargets (numbersNumber rows ::ᵥ nil) = encodeResult (mapped rows)

def ExactRawInsertedTargets : Prop :=
  ∀ raw, evaluate insertedTargets (raw ::ᵥ nil) =
    encodeResult ((unpack raw).bind mapped)

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsMapTargets
