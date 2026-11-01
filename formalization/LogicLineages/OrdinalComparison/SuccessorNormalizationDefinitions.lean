module
public import LogicLineages.OrdinalComparison.OrdinalSuccessorProgramDefinitions
public import LogicLineages.OrdinalComparison.SuccessorWordProgramDefinitions
public import LogicLineages.OrdinalComparison.RawComparisonDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Prefix-source code, current actual outer exponent code, accumulated
source-domain tail. All fields are numerical, with source correctness owed. -/
abbrev SuccessorNormalizationState := Nat × Nat × Nat

def encodedSuccessorNormalizationActive (lower : Nat) (s : SuccessorNormalizationState) : Prop :=
  rawComparisonCode s.2.1 lower=2 ∧ 0<encodedOrdinalFiniteRemainder s.2.1

instance (lower : Nat) (s : SuccessorNormalizationState) :
    Decidable (encodedSuccessorNormalizationActive lower s) :=
  inferInstanceAs (Decidable (rawComparisonCode s.2.1 lower=2 ∧ 0<encodedOrdinalFiniteRemainder s.2.1))

def encodedSuccessorNormalizationStep (lower c : Nat) (s : SuccessorNormalizationState) :
    SuccessorNormalizationState :=
  if encodedSuccessorNormalizationActive lower s then
    let pred := encodedOrdinalSuccessorPredecessor s.2.1
    let wordPrefix := encodedComparisonAppendKernel s.1 s.2.1 (c+1+rawNormCode pred)
    (wordPrefix,pred,max s.2.2 (encodedOneVariableComparisonDomainBound
      (encodedComparisonAppendKernel wordPrefix pred c)))
  else s

def encodedSuccessorNormalizationInitial (source eta c : Nat) : SuccessorNormalizationState :=
  (source,eta,max 1 (encodedOneVariableComparisonDomainBound (encodedComparisonAppendKernel source eta c)))

/-- Explicit bounded iteration, not a partial search or supplied terminating
normalizer. Exact source successor steps lower the additive exponent norm. -/
def encodedSuccessorNormalizationTrace (source eta lower c : Nat) (steps : Nat) :
    SuccessorNormalizationState :=
  (encodedSuccessorNormalizationStep lower c)^[steps]
    (encodedSuccessorNormalizationInitial source eta c)

/-- Final literal range-source code, final outer exponent code, and genuine
whole-trace domain threshold. Fuel is computed from the original exponent. -/
def encodedSuccessorNormalization (source eta lower c : Nat) : Nat × Nat × Nat :=
  let s := encodedSuccessorNormalizationTrace source eta lower c (rawNormCode eta)
  (encodedComparisonAppendKernel s.1 s.2.1 c,s.2.1,s.2.2)

end LogicLineages.OrdinalComparison
