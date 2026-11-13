module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.PairCongruenceProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.ComparisonProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.StepEquationsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph

/-- Actual pair application inside the step, normalized only by projection laws. -/
theorem candidateEquation {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨5,candidate⟩) (b previous a code seed : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (b ::ᵥ previous ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil))
        (call (tag+1) (a ::ᵥ b ::ᵥ nil)))) := by
  apply SixSol20261112.Fuel.Equations.compositionValues p tag HistoryCodec.pair candidateArguments ht
    (b ::ᵥ previous ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil) (a ::ᵥ b ::ᵥ nil)
  intro i
  have hc := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.pair candidateArguments ht i
  cases i using Fin.cases with
  | zero => exact SixSol20261112.Fuel.Equations.projection p _ (2 : Fin 5) hc _
  | succ i => cases i using Fin.cases with
    | zero => exact SixSol20261112.Fuel.Equations.projection p _ (0 : Fin 5) hc _
    | succ i => exact Fin.elim0 i

def forwardPairTag (tag : Nat) := tag + argumentTag HistoryCodec.difference forwardArguments 0 + 1
def backwardPairTag (tag : Nat) := tag + argumentTag HistoryCodec.difference backwardArguments 1 + 1

theorem forwardPairInstalled {n : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨5,forward⟩) :
    (nodes p)[forwardPairTag tag]? = some ⟨2,HistoryCodec.pair⟩ := by
  have hc := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.difference forwardArguments ht 0
  exact SixSol20261112.Fuel.Equations.functionChild p _ HistoryCodec.pair candidateArguments hc

theorem backwardPairInstalled {n : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨5,backward⟩) :
    (nodes p)[backwardPairTag tag]? = some ⟨2,HistoryCodec.pair⟩ := by
  have hc := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.difference backwardArguments ht 1
  exact SixSol20261112.Fuel.Equations.functionChild p _ HistoryCodec.pair candidateArguments hc

theorem forwardEquation {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨5,forward⟩) (b previous a code seed : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (b ::ᵥ previous ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil))
        (call (tag+1) (call (forwardPairTag tag) (a ::ᵥ b ::ᵥ nil) ::ᵥ code ::ᵥ nil)))) := by
  have hc := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.difference forwardArguments ht 0
  obtain ⟨hp⟩ := candidateEquation p _ hc b previous a code seed
  apply SixSol20261112.Fuel.Equations.compositionValues p tag HistoryCodec.difference forwardArguments ht
    (b ::ᵥ previous ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil)
    (call (forwardPairTag tag) (a ::ᵥ b ::ᵥ nil) ::ᵥ code ::ᵥ nil)
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨hp⟩
  | succ i => cases i using Fin.cases with
    | zero =>
        have h := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.difference forwardArguments ht 1
        exact SixSol20261112.Fuel.Equations.projection p _ (3 : Fin 5) h _
    | succ i => exact Fin.elim0 i

theorem backwardEquation {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨5,backward⟩) (b previous a code seed : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (b ::ᵥ previous ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil))
        (call (tag+1) (code ::ᵥ call (backwardPairTag tag) (a ::ᵥ b ::ᵥ nil) ::ᵥ nil)))) := by
  have hc := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.difference backwardArguments ht 1
  obtain ⟨hp⟩ := candidateEquation p _ hc b previous a code seed
  apply SixSol20261112.Fuel.Equations.compositionValues p tag HistoryCodec.difference backwardArguments ht
    (b ::ᵥ previous ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil)
    (code ::ᵥ call (backwardPairTag tag) (a ::ᵥ b ::ᵥ nil) ::ᵥ nil)
  intro i
  cases i using Fin.cases with
  | zero =>
      have h := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.difference backwardArguments ht 0
      exact SixSol20261112.Fuel.Equations.projection p _ (3 : Fin 5) h _
  | succ i => cases i using Fin.cases with
    | zero => exact ⟨hp⟩
    | succ i => exact Fin.elim0 i

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.StepEquationsProof
