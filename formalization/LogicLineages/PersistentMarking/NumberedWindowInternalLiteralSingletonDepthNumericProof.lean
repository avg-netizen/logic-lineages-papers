module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafProof
public import LogicLineages.PersistentMarking.NumberedWindowSingletonAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowSingletonProgramProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonDepthNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalApplicationValidityStackEvaluationProof (zeroEvaluation)
open NumberedWindowAddressAlgorithm (typeBit)
open NumberedWindowFieldAlgorithm (unpackNode packNode)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode nodePacked)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowSingletonAlgorithm
open NumberedWindowInternalLiteralBetaLeafProof (InstanceFit instanceValue)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (vectorThree)

def depthInstanceValue (a d q : Nat) : Nat :=
  (((output a d q).1).map Nat.succ).getD 0

def DepthInstanceFit (U : Program 3) : Prop :=
  ∀ a d q, evaluate U (a ::ᵥ d ::ᵥ q ::ᵥ nil) = depthInstanceValue a d q

theorem exact_LiteralDepthInstance : ∃ U : Program 3, DepthInstanceFit U := by
  let X := List.Vector Nat 3
  have left : Primrec (fun v : X => v.head) := Primrec.vector_head
  have tail : Primrec (fun v : X => v.tail) := Primrec.vector_tail
  have mid : Primrec (fun v : X => v.tail.head) := Primrec.vector_head.comp tail
  have last : Primrec (fun v : X => v.tail.tail.head) :=
    Primrec.vector_head.comp (Primrec.vector_tail.comp tail)
  have full := NumberedWindowSingletonProgramProof.outputPrim.comp (left.pair (mid.pair last))
  have result := Primrec.fst.comp full
  have packed := (Primrec.option_map₁ Primrec.succ).comp result
  obtain ⟨p,ok⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 3 _
    (Primrec.option_getD.comp packed (Primrec.const 0))
  exact ⟨p,fun a d q => ok (a ::ᵥ d ::ᵥ q ::ᵥ nil)⟩

def zeroDepthInstance (U : Program 3) : Program 2 :=
  .composition U ![.projection 0,constantZero 2,.projection 1]

theorem exact_ZeroDepthInstance (U : Program 3) (fit : DepthInstanceFit U) :
    InstanceFit (zeroDepthInstance U) := by
  intro a q
  rw [zeroDepthInstance,evaluate,vectorThree]
  change evaluate U (a ::ᵥ evaluate (constantZero 2) (a ::ᵥ q ::ᵥ nil) ::ᵥ q ::ᵥ nil) = _
  rw [zeroEvaluation,fit a 0 q]
  rfl

theorem exact_OriginalSingletonFree (a d q ty id : Nat)
    (node : unpackNode q = some (0,[ty,id])) :
    (output a d q).1 = if (syntaxBits a).1 && typeBit ty then some q else none := by
  have shape : (syntaxBits q).1 = typeBit ty := by
    simp only [syntaxBits,NumberedWindowSyntaxAlgorithm.termNext,node,Option.any_some,
      NumberedWindowSyntaxAlgorithm.termParts]
  have field : (computed a d q q 0).1 = q := by
    simp only [computed,next,node,Option.map_some,Option.getD_some,termParts,
      NumberedWindowShiftAlgorithm.termParts]
    exact (codeOfNode node).symm
  simp only [output,shape,field]

theorem exact_OriginalSingletonBottom (a d q ty : Nat)
    (node : unpackNode q = some (3,[ty])) :
    (output a d q).1 = if (syntaxBits a).1 && typeBit ty then some q else none := by
  have shape : (syntaxBits q).1 = typeBit ty := by
    simp only [syntaxBits,NumberedWindowSyntaxAlgorithm.termNext,node,Option.any_some,
      NumberedWindowSyntaxAlgorithm.termParts]
  have field : (computed a d q q 0).1 = q := by
    simp only [computed,next,node,Option.map_some,Option.getD_some,termParts,
      NumberedWindowShiftAlgorithm.termParts]
    exact (codeOfNode node).symm
  simp only [output,shape,field]

/-- Before the discharged index nothing changes; at the index use the
literal capture-avoiding shift; above it lower exactly one index.
Syntactically malformed inputs uniformly return failure. -/
theorem exact_OriginalSingletonBound (a d q ty id : Nat)
    (node : unpackNode q = some (1,[ty,id])) :
    (output a d q).1 = if (syntaxBits a).1 && typeBit ty then some
      (if id < d then q else if id = d then ((NumberedWindowShiftAlgorithm.output d 0 a).1).getD 0
        else packNode 1 [ty,id.pred]) else none := by
  have shape : (syntaxBits q).1 = typeBit ty := by
    simp only [syntaxBits,NumberedWindowSyntaxAlgorithm.termNext,node,Option.any_some,
      NumberedWindowSyntaxAlgorithm.termParts]
  have code := codeOfNode node
  simp only [output,shape,computed,next,node,Option.map_some,Option.getD_some,termParts,if_true,
    Nat.add_zero,List.getD_cons_succ,List.getD_cons_zero]
  rw [← code]

#print axioms exact_LiteralDepthInstance
#print axioms exact_ZeroDepthInstance
#print axioms exact_OriginalSingletonFree
#print axioms exact_OriginalSingletonBottom
#print axioms exact_OriginalSingletonBound
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonDepthNumericProof
