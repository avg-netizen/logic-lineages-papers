module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawSelectionTargets
import LogicLineages.PersistentMarking.NumberedWindowPositivePathParserPrograms
import LogicLineages.PersistentMarking.NumberedWindowScalarProgramProof
import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawPackedWindowProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowScalarProgramProof (admittedPrim)
open NumberedWindowPositivePathParserPrograms (fieldsPrim)
open NumberedWindowSyntaxShapePrograms (anyOption)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow packedWindow)

private theorem coord (i : Fin 3) :
    Primrec (fun v : List.Vector Nat 3 => v.get i) :=
  Primrec.vector_get.comp Primrec.id (Primrec.const i)

private theorem packedAdmissionPrim (s : Settings) :
    Primrec (fun v : List.Vector Nat 3 => packedWindow s (v.get 0) (v.get 1) (v.get 2)) := by
  let V := List.Vector Nat 3
  let P := V × List Nat
  have ty : Primrec (fun p : P => p.1.get 1) := (coord (1 : Fin 3)).comp Primrec.fst
  have term : Primrec (fun p : P => p.1.get 2) := (coord (2 : Fin 3)).comp Primrec.fst
  have data : Primrec (fun p : P => (p.2,p.1.get 1,p.1.get 2)) :=
    Primrec.snd.pair (ty.pair term)
  exact anyOption (fieldsPrim.comp (coord (0 : Fin 3))) ((admittedPrim s).comp data).to₂

/-- Real packed-context window bit. The literal option traversal uses
false for a malformed code and the actual list for every successful one. -/
theorem packedWindowWitness (s : Settings) : ∃ wp : Program 3, ActualPackedWindow s wp := by
  let value (v : List.Vector Nat 3) := (packedWindow s (v.get 0) (v.get 1) (v.get 2)).toNat
  have h : Primrec value := by
    apply (Primrec.cond (packedAdmissionPrim s) (Primrec.const (1 : Nat)) (Primrec.const 0)).of_eq
    intro v
    dsimp only [value]
    cases packedWindow s (v.get 0) (v.get 1) (v.get 2) <;> rfl
  obtain ⟨wp,hp⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 3 value h
  refine ⟨wp,?_⟩
  intro ctx ty q
  exact hp (ctx ::ᵥ ty ::ᵥ q ::ᵥ nil)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawPackedWindowProof
