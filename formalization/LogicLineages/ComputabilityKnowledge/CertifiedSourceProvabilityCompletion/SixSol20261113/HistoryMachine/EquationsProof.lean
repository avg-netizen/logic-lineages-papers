module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HistoryMachine.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.EquationsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryMachine.Equations
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPRDefiningEquations
open GorbowPRChildTags List.Vector
open SixSol20261112.HistoryMachine
open SixSol20261112.Fuel
open NamedArithmeticGraph

private def indices : Fin 3 → Fin 5 :=
  Fin.cases 1 (Fin.cases 3 (Fin.cases 4 Fin.elim0))

private theorem argumentsProjection (i : Fin 3) :
    iterationArguments i = Program.projection (indices i) := by
  cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
    | zero => rfl
    | succ i => cases i using Fin.cases with
      | zero => rfl
      | succ i => exact Fin.elim0 i

private theorem argumentVector {ctx : Nat} (count previous state index fuel : Term ctx) :
    (List.Vector.ofFn fun i =>
      (count ::ᵥ previous ::ᵥ state ::ᵥ index ::ᵥ fuel ::ᵥ nil).get (indices i)) =
        previous ::ᵥ index ::ᵥ fuel ::ᵥ nil := by
  apply List.Vector.ext
  intro i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
    | zero => rfl
    | succ i => cases i using Fin.cases with
      | zero => rfl
      | succ i => exact Fin.elim0 i

theorem zero {n ctx : Nat} (p : Program n) tag (kernel : Program 3)
    (ht : (nodes p)[tag]? = some ⟨4,iterator kernel⟩) (state index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (iterationCall tag .zero state index fuel) state)) := by
  have hb : (nodes p)[tag+1]? = some ⟨3,iterationBase⟩ :=
    GorbowPRSubtree.Proof.lookupTransport n p tag ⟨4,iterator kernel⟩ 1
      ⟨3,iterationBase⟩ ht (GorbowPRChildTags.Proof.recursionBase 3 iterationBase (iterationStep kernel))
  obtain ⟨hz⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation
    n p tag 3 iterationBase (iterationStep kernel) ht ctx (state ::ᵥ index ::ᵥ fuel ::ᵥ nil)
  obtain ⟨hp⟩ := SixSol20261112.Fuel.Equations.projection p (tag+1) (0 : Fin 3) hb
    (state ::ᵥ index ::ᵥ fuel ::ᵥ nil)
  exact ⟨Logic.trans _ _ _ hz hp⟩

theorem successor {n ctx : Nat} (p : Program n) tag (kernel : Program 3)
    (ht : (nodes p)[tag]? = some ⟨4,iterator kernel⟩) (count state index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (iterationCall tag (.succ count) state index fuel)
        (call (tag + stepTag iterationBase + 1)
          (iterationCall tag count state index fuel ::ᵥ index ::ᵥ fuel ::ᵥ nil)))) := by
  have hs := SixSol20261112.Fuel.Equations.recursionStepChild p tag
    iterationBase (iterationStep kernel) ht
  obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation
    n p tag 3 iterationBase (iterationStep kernel) ht ctx count (state ::ᵥ index ::ᵥ fuel ::ᵥ nil)
  obtain ⟨hc⟩ := SixSol20261112.Fuel.Equations.compositionProjections p
    (tag + stepTag iterationBase) kernel iterationArguments hs indices argumentsProjection
    (count ::ᵥ iterationCall tag count state index fuel ::ᵥ state ::ᵥ index ::ᵥ fuel ::ᵥ nil)
  rw [argumentVector] at hc
  exact ⟨Logic.trans _ _ _ hr hc⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryMachine.Equations
