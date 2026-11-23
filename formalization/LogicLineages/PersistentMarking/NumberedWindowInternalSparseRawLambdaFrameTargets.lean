module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaFrame
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalSparsePathEnvelope (nodeGood)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw frameSlot sameSlot encodeFrame)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowFieldAlgorithm (unpackNode packNode)
open NumberedWindowRawContextAlgorithm (Frame RawRoot next tick)

def termShape : Program 1 := nodeGood (literal 1 2) 2
def witnessShape : Program 1 := nodeGood (literal 1 1) 1

/-- Exact original raw constructor order. Only the stored lambda domain,
not the body, is required to agree on the two endpoint tapes. -/
def frameGood : Program 3 :=
  conjunction (onRaw witnessShape 1)
    (conjunction (onRaw termShape 0) (conjunction (onRaw termShape 2) (sameSlot 0)))

def emitFrame : Program 3 :=
  .composition .succ (fun _ : Fin 1 =>
    consOf (frameSlot 1 0) (consOf (frameSlot 0 1) (consOf (frameSlot 1 2) (constantZero 3))))

def chosenFrame : Program 3 := branch frameGood (constantZero 3) emitFrame

def tagOneNext (q w r : Nat) : Option Frame :=
  match unpackNode w with
  | some (1,[child]) => next 1 [child] q r
  | _ => none

def endpointTerm {α : Type} (dom body : OTerm α) : OTerm α :=
  rawCons (numeral 2) (packedBody [dom,body])

def witnessTerm {α : Type} (child : OTerm α) : OTerm α :=
  rawCons (numeral 1) (packedBody [child])

abbrev liftedTape {α : Type} (dom src child dst : OTerm α) : Fin 3 → OTerm α :=
  ![endpointTerm dom src,witnessTerm child,endpointTerm dom dst]

def ExactAllRawLambdaFrame : Prop :=
  ∀ q w r, evaluate chosenFrame (q ::ᵥ w ::ᵥ r ::ᵥ nil) = encodeFrame (tagOneNext q w r)

def ExactLiteralLambdaTick : Prop :=
  ∀ (root : RawRoot) (status : Bool) (dom src child dst : Nat),
    tick root (status,some (packNode 2 [dom,src],packNode 1 [child],packNode 2 [dom,dst])) =
      (false,some (src,child,dst))

def ExactOpenLiteralLambdaFrame : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (dom src child dst : OTerm α),
    Nonempty (Derivation body Γ (programGraph chosenFrame (frameValueTerm src child dst)
      (liftedTape dom src child dst)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaFrame
