module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowStepTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawPackedWindowProof
import LogicLineages.PersistentMarking.NumberedWindowAnnotationProgramProof
import LogicLineages.PersistentMarking.NumberedWindowAddressProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowStepPrograms
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowAddressAlgorithm (typeBit)
open NumberedWindowInternalAuxWindowMemoTargets
open NumberedWindowInternalAuxWindowStepTargets
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparseTypedRawTargets (packedWindow)
open NumberedWindowInternalSparseTypedRawPackedWindowProof (packedWindowWitness)
open NumberedWindowAnnotationProgramProof (annotationPrim)
open NumberedWindowAddressProgramProof (validType)

private theorem guardNotOutside (s : Settings) : Primrec (typeGuard s) := by
  have contains : Primrec₂ (List.contains (α := Nat)) := by
    have has : PrimrecRel (fun (xs : List Nat) (n : Nat) => n ∈ xs) :=
      (Primrec.eq : PrimrecRel (Eq : Nat → Nat → Prop)).exists_mem_list.of_eq (by simp)
    apply has.decide.to₂.of_eq
    intro xs n
    apply Bool.eq_iff_iff.mpr
    simp
  exact Primrec.and.comp validType (contains.comp (Primrec.const s.window.1) Primrec.id)

private theorem intrinsicPrimitive (s : Settings) (W : Program 3)
    (window : NumberedWindowInternalSparseTypedRawTargets.ActualPackedWindow s W) :
    Primrec (fun v : List.Vector Nat 2 => intrinsicWindow s v.head v.tail.head) := by
  let V := List.Vector Nat 2
  have ctx : Primrec (fun v : V => v.head) := Primrec.vector_head
  have raw : Primrec (fun v : V => v.tail.head) := Primrec.vector_head.comp Primrec.vector_tail
  have ty : Primrec (fun v : V => intrinsicType v.tail.head) :=
    (Primrec.fst.comp annotationPrim).comp raw
  have tape := Primrec.vector_cons.comp ctx
    (Primrec.vector_cons.comp ty (Primrec.vector_cons.comp raw (Primrec.const List.Vector.nil)))
  have actual := (Proof.primitiveEvaluation 3 W).comp tape
  apply (Primrec.ite (Primrec.eq.comp actual (Primrec.const 1))
    (Primrec.succ.comp ty) (Primrec.const 0)).of_eq
  intro v
  change (if evaluate W (v.head ::ᵥ intrinsicType v.tail.head ::ᵥ v.tail.head ::ᵥ nil) = 1
    then intrinsicType v.tail.head + 1 else 0) = _
  rw [window]
  cases read : packedWindow s v.head (intrinsicType v.tail.head) v.tail.head <;>
    simp [intrinsicWindow,read]

theorem exact_WindowPrimitiveLeaves : ExactWindowPrimitiveLeaves := by
  intro s
  obtain ⟨W,window⟩ := packedWindowWitness s
  obtain ⟨base,evalBase⟩ := Proof.allPrimitiveFunctions 2 _ (intrinsicPrimitive s W window)
  have h : Primrec (fun n => (typeGuard s n).toNat) := by
    apply (Primrec.cond (guardNotOutside s) (Primrec.const 1) (Primrec.const 0)).of_eq
    intro n
    cases typeGuard s n <;> rfl
  obtain ⟨T,evalT⟩ := (Proof.unaryCorrespondence _).mp h
  exact ⟨base,T,fun ctx raw => evalBase (ctx ::ᵥ raw ::ᵥ nil),evalT⟩

#print axioms exact_WindowPrimitiveLeaves

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowStepPrograms
