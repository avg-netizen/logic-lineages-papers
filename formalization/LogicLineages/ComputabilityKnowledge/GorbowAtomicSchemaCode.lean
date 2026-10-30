module

public import LogicLineages.ComputabilityKnowledge.GorbowAtomicParameterCode
public import LogicLineages.ComputabilityKnowledge.GorbowAtomicAnnotation

@[expose] public section
/-! An annotated compiler of the literal atomic FS schema family. This is not
an unannotated axiom-membership decision or an adequate Base/DCB presentation.
The annotation retains the original ambient context and precise ordered names. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowAtomicSchemaCode
open GorbowCodeConstructors GorbowAtomicParameterCode

def bodyRaw (m : Nat) (raw names : List Nat) : Option (List Nat) := do
  let rhs ← GorbowSubstitutionCode.substituteFormulaCode m names.length (valueSlots m names) raw
  let lhs := unary 5 (instanceRaw m raw names)
  pure (binary 8 (binary 7 lhs rhs) (binary 7 rhs lhs))

def compileRaw (m : Nat) (raw names : List Nat) : Option (List Nat) :=
  if GorbowAtomicAnnotation.valid m raw names then
    (bodyRaw m raw names).map (GorbowRegistryTermCode.closeRaw names.length)
  else none

def compileNumber (m : Nat) (raw names : List Nat) : Option Nat :=
  (compileRaw m raw names).map GorbowSortedSyntaxCode.formulaRawNumber
end LogicLineages.ComputabilityKnowledge.GorbowAtomicSchemaCode
