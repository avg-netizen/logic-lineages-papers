module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoWindowNumericProof
import LogicLineages.PersistentMarking.NumberedWindowAnnotationProgramProof
import LogicLineages.PersistentMarking.NumberedWindowAddressProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoInputsProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowAnnotationAlgorithm (annotations)
open NumberedWindowAnnotationProgramProof (annotationPrim)
open NumberedWindowAddressProgramProof (validType)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow packedWindow)
open NumberedWindowInternalAuxWindowMemoTargets (intrinsicWindow intrinsicType IntrinsicWindowCalibrated typeGuard)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)
open NumberedWindowInternalSparsePathEnvelope (run)

private theorem coord {n : Nat} (i : Fin n) :
    Primrec (fun v : List.Vector Nat n => v.get i) :=
  Primrec.vector_get.comp Primrec.id (Primrec.const i)

private theorem containsPrim : Primrec₂ (List.contains (α := Nat)) := by
  have mem : PrimrecRel (fun (xs : List Nat) (a : Nat) => a ∈ xs) :=
    (Primrec.eq : PrimrecRel (Eq : Nat → Nat → Prop)).exists_mem_list.of_eq (by simp)
  apply mem.decide.to₂.of_eq
  intro xs a
  apply Bool.eq_iff_iff.mpr
  simp

theorem exact_SyntaxMemoTypeInput (s : Settings) : ∃ T : Program 1, TypeGuardCalibrated s T := by
  let f (v : List.Vector Nat 1) := (typeGuard s (v.get 0)).toNat
  have valid := validType.comp (coord (0 : Fin 1))
  have listed := containsPrim.comp (Primrec.const s.window.1) (coord (0 : Fin 1))
  have both : Primrec (fun v : List.Vector Nat 1 => typeGuard s (v.get 0)) :=
    Primrec.and.comp valid listed
  have prim : Primrec f := by
    apply (Primrec.cond both (Primrec.const (1 : Nat)) (Primrec.const 0)).of_eq
    intro v
    dsimp only [f]
    cases typeGuard s (v.get 0) <;> rfl
  obtain ⟨T,h⟩ := Proof.allPrimitiveFunctions 1 f prim
  exact ⟨T, fun n => h (n ::ᵥ nil)⟩

/-- The intrinsic base can be chosen from the already calibrated
original packed window callback and the original annotation evaluator.
It is not an extra existential promise imposed on `ValidWindow`. -/
theorem exact_SyntaxMemoIntrinsicInput (s : Settings) (W : Program 3) (fit : ActualPackedWindow s W) :
    ∃ base : Program 2, IntrinsicWindowCalibrated s base := by
  let V := List.Vector Nat 2
  let a (v : V) := intrinsicType (v.get 1)
  let f (v : V) := intrinsicWindow s (v.get 0) (v.get 1)
  have typePrim : Primrec a := Primrec.fst.comp (annotationPrim.comp (coord (1 : Fin 2)))
  have pr := Proof.primitiveEvaluation 3 W
  have values : Primrec (fun v : V => evaluate W (v.get 0 ::ᵥ a v ::ᵥ v.get 1 ::ᵥ nil)) :=
    pr.comp (Primrec.vector_cons.comp (coord 0) (Primrec.vector_cons.comp typePrim
      (Primrec.vector_cons.comp (coord 1) (Primrec.const nil))))
  have fprim : Primrec f := by
    apply (Primrec.ite (Primrec.eq.comp values (Primrec.const 1))
      (Primrec.succ.comp typePrim) (Primrec.const 0)).of_eq
    intro v
    dsimp only [f,intrinsicWindow,a]
    rw [fit]
    cases packedWindow s (v.get 0) (intrinsicType (v.get 1)) (v.get 1) <;> rfl
  obtain ⟨B,h⟩ := Proof.allPrimitiveFunctions 2 f fprim
  exact ⟨B,fun ctx raw => h (ctx ::ᵥ raw ::ᵥ nil)⟩

#print axioms exact_SyntaxMemoTypeInput
#print axioms exact_SyntaxMemoIntrinsicInput
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoInputsProof
