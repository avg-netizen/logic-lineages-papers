module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonAtomsNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaLexicalGateNumericProof
import LogicLineages.PersistentMarking.NumberedWindowShiftProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundMachineProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch constantZero)
open InternalEqualityTest (equalityTest)
open InternalLessThan (ltTest)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparsePathEnvelope (nodeGood field applyUnary)
open NumberedWindowInternalFreshProbeDispatchProgram (literal predOne)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalLiteralSingletonAtomsNumericProof
open NumberedWindowShiftAlgorithm (output)

def shiftHitValue (a d : Nat) : Nat := ((output d 0 a).1).getD 0 + 1

def ShiftHitFit (H : Program 2) : Prop :=
  ∀ a d, evaluate H (a ::ᵥ d ::ᵥ nil) = shiftHitValue a d

theorem exact_LiteralShiftHit : ∃ H : Program 2, ShiftHitFit H := by
  let X := List.Vector Nat 2
  have iv : Primrec (fun v : X => v.head) := Primrec.vector_head
  have localDepth : Primrec (fun v : X => v.tail.head) :=
    Primrec.vector_head.comp (Primrec.vector_tail : Primrec (fun v : X => v.tail))
  have full := NumberedWindowShiftProgramProof.outputPrim.comp (localDepth.pair ((Primrec.const 0).pair iv))
  have first := Primrec.fst.comp full
  have packed := Primrec.succ.comp (Primrec.option_getD.comp first (Primrec.const 0))
  obtain ⟨p,ok⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 2 _ packed
  exact ⟨p,fun a d => ok (a ::ᵥ d ::ᵥ nil)⟩

def boundShape : Program 1 := nodeGood (literal 1 1) 2
def boundType : Program 3 := onRaw (field 0) 2
def boundIndex : Program 3 := onRaw (field 1) 2
def boundBeforeDepth : Program 3 := .composition ltTest ![boundIndex,.projection 1]
def boundAtDepth : Program 3 := .composition equalityTest ![boundIndex,.projection 1]

def loweredIndex : Program 3 := onRaw (applyUnary predOne (field 1)) 2
def boundLowerCode : Program 3 :=
  consOf (literal 3 1) (consOf boundType (consOf loweredIndex (constantZero 3)))
def boundLowered : Program 3 := .composition .succ (fun _ : Fin 1 => boundLowerCode)

def directInsertion : Program 3 := .composition .succ (fun _ : Fin 1 => .projection 0)
def shiftedInsertion (H : Program 2) : Program 3 :=
  branch (.projection 1) directInsertion (.composition H ![.projection 0,.projection 1])

def boundInstance (H : Program 2) : Program 3 :=
  branch boundBeforeDepth (branch boundAtDepth boundLowered (shiftedInsertion H)) retainSingleton

def singletonBoundDispatch (H : Program 2) (U : Program 3) : Program 3 :=
  branch (onRaw boundShape 2) U (boundInstance H)

/-- Atom and bound cases are now physical, including the exact index
decrement and capture-avoiding shift. The outer program still returns
failure on either syntactically malformed operand. -/
def singletonBound (V : Program 1) (H : Program 2) (U : Program 3) : Program 3 :=
  singletonAtoms V (branch (singletonSyntax V) (constantZero 3) (singletonBoundDispatch H U))

#print axioms exact_LiteralShiftHit
#print axioms singletonBound
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundMachineProof
