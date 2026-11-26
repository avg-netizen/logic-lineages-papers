module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootDispatchNumericProof
import LogicLineages.PersistentMarking.NumberedWindowSingletonProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (conjunction)
open InternalEqualityTest (equalityTest)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw frameSlot)
open NumberedWindowInternalSparsePathEnvelope (field nodeGood)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalLiteralAuxFallback (sourceIsAux)
open NumberedWindowInternalLiteralRootDispatchNumericProof (guard)
open NumberedWindowSingletonAlgorithm (output)

/-- The original singleton substitution at the discharged binder. Zero is
only failure, and a successful instance is successor-packed. -/
def instanceValue (a body : Nat) : Nat :=
  (((output a 0 body).1).map Nat.succ).getD 0

def InstanceFit (U : Program 2) : Prop :=
  ∀ a body, evaluate U (a ::ᵥ body ::ᵥ nil) = instanceValue a body

theorem exact_LiteralSingletonInstance : ∃ U : Program 2, InstanceFit U := by
  let A := List.Vector Nat 2
  have left : Primrec (fun v : A => v.head) := Primrec.vector_head
  have right : Primrec (fun v : A => v.tail.head) := Primrec.vector_head.comp
    (Primrec.vector_tail : Primrec (fun v : A => v.tail))
  have atDepth := NumberedWindowSingletonProgramProof.outputPrim.comp (left.pair ((Primrec.const 0).pair right))
  have first := Primrec.fst.comp atDepth
  have packed := (Primrec.option_map₁ Primrec.succ).comp first
  obtain ⟨p,check⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 2 _
    (Primrec.option_getD.comp packed (Primrec.const 0))
  exact ⟨p,fun a body => check (a ::ᵥ body ::ᵥ nil)⟩

def rawFunction : Program 3 := frameSlot 2 0

def rawLambdaShape : Program 1 := nodeGood (literal 1 2) 2

def functionShape : Program 3 := .composition rawLambdaShape (fun _ : Fin 1 => rawFunction)

def lambdaField (n : Nat) : Program 3 := .composition (field n) (fun _ : Fin 1 => rawFunction)

def domainMatch : Program 3 := .composition equalityTest ![frameSlot 0 0,lambdaField 0]

def instanceAt (U : Program 2) : Program 3 := .composition U ![frameSlot 3 0,lambdaField 1]

def nextCode : Program 3 := .composition .succ (fun _ : Fin 1 => .projection 2)

def targetMatch (U : Program 2) : Program 3 := .composition equalityTest ![instanceAt U,nextCode]

/-- A literal, openable beta leaf. Its syntax and frame tests are actual
components. The exact successful substitution can be read from its tape. -/
def literalBetaLeaf (V : Program 1) (U : Program 2) : Program 3 :=
  conjunction (onRaw V 0) (conjunction (onRaw V 2)
    (conjunction sourceIsAux (conjunction functionShape (conjunction domainMatch (targetMatch U)))))

def withBetaLeaf (V : Program 1) (U : Program 2) (leaf : Nat → Program 3) (tag : Nat) : Program 3 :=
  if tag = 6 then conjunction (guard 6 0) (literalBetaLeaf V U) else leaf tag

#print axioms exact_LiteralSingletonInstance
#print axioms literalBetaLeaf
#print axioms withBetaLeaf
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafProof
