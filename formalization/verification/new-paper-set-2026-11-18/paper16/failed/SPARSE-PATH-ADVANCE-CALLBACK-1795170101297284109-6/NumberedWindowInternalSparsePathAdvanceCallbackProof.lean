module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets
import LogicLineages.PersistentMarking.NumberedWindowPositivePathParserPrograms
import LogicLineages.PersistentMarking.NumberedWindowRawContextProgramProof
import LogicLineages.PersistentMarking.NumberedWindowRootDispatchProgramProof
import LogicLineages.PersistentMarking.NumberedWindowConcreteRulePrograms
import LogicLineages.PersistentMarking.NumberedWindowScalarProgramProof
import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceCallbackProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathAdvanceTargets
open NumberedWindowPositivePathParserPrograms (fieldsPrim)
open NumberedWindowRawContextProgramTargets (StepInput)
open NumberedWindowSyntaxShapePrograms (anyOption)

private theorem coord {n : Nat} (i : Fin n) :
    Primrec (fun v : List.Vector Nat n => v.get i) :=
  Primrec.vector_get.comp Primrec.id (Primrec.const i)

private theorem concreteRaw (entries : Entries) (s : Settings) :
    Primrec (fun p : StepInput =>
      NumberedWindowConcreteCheckers.step entries s p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) :=
  NumberedWindowRawContextProgramProof.windowStepPrim
    (NumberedWindowRootDispatchProgramProof.checkPrim
      (NumberedWindowConcreteRulePrograms.primitive entries s.window.2))
    (NumberedWindowScalarProgramProof.admittedPrim s)

private theorem rawPrim (entries : Entries) (s : Settings) :
    Primrec (fun v : List.Vector Nat 5 =>
      packedRaw entries s (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4)) := by
  let V := List.Vector Nat 5
  let P := V × List Nat
  have t : Primrec (fun p : P => p.1.get 1) := (coord (1 : Fin 5)).comp Primrec.fst
  have q : Primrec (fun p : P => p.1.get 2) := (coord (2 : Fin 5)).comp Primrec.fst
  have w : Primrec (fun p : P => p.1.get 3) := (coord (3 : Fin 5)).comp Primrec.fst
  have r : Primrec (fun p : P => p.1.get 4) := (coord (4 : Fin 5)).comp Primrec.fst
  have data : Primrec (fun p : P => (p.2,p.1.get 1,p.1.get 2,p.1.get 3,p.1.get 4)) :=
    Primrec.snd.pair (t.pair (q.pair (w.pair r)))
  exact anyOption (fieldsPrim.comp (coord (0 : Fin 5))) ((concreteRaw entries s).comp data).to₂

private theorem leastPrim (s : Settings) :
    Primrec (fun v : List.Vector Nat 3 => packedLeast s (v.get 0) (v.get 1) (v.get 2)) := by
  let V := List.Vector Nat 3
  let P := V × List Nat
  have ty : Primrec (fun p : P => p.1.get 1) := (coord (1 : Fin 3)).comp Primrec.fst
  have q : Primrec (fun p : P => p.1.get 2) := (coord (2 : Fin 3)).comp Primrec.fst
  have data : Primrec (fun p : P => (p.2,p.1.get 1,p.1.get 2)) :=
    Primrec.snd.pair (ty.pair q)
  exact Primrec.option_bind (fieldsPrim.comp (coord (0 : Fin 3)))
    ((NumberedWindowScalarProgramProof.leastPrim s).comp data).to₂

theorem rawWitness (entries : Entries) (s : Settings) :
    ∃ raw : Program 5, ActualRawCalibration entries s raw := by
  let value (v : List.Vector Nat 5) :=
    if packedRaw entries s (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4) then 1 else 0
  have h : Primrec value := by
    apply (Primrec.cond (rawPrim entries s) (Primrec.const (1 : Nat)) (Primrec.const 0)).of_eq
    intro v
    cases b : packedRaw entries s (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4) <;>
      simp [value,b]
  obtain ⟨p,hp⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 5 value h
  exact ⟨p,fun ctx ty q w r => hp (ctx ::ᵥ ty ::ᵥ q ::ᵥ w ::ᵥ r ::ᵥ nil)⟩

theorem leastWitness (s : Settings) : ∃ least : Program 3, ActualLeastCalibration s least := by
  let value (v : List.Vector Nat 3) := encodeState (packedLeast s (v.get 0) (v.get 1) (v.get 2))
  have h : Primrec value := by
    apply (Primrec.encode.comp (leastPrim s)).of_eq
    intro v
    cases packedLeast s (v.get 0) (v.get 1) (v.get 2) <;> rfl
  obtain ⟨p,hp⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 3 value h
  exact ⟨p,fun ctx ty q => hp (ctx ::ᵥ ty ::ᵥ q ::ᵥ nil)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceCallbackProof
