module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedSelfApplication
public import LogicLineages.ComputabilityKnowledge.GorbowSubstitutionCode
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
/-! Genuine two-input self-application with one RETAINED formula parameter.
The old sorted selfApply is Formula1→Sentence only. This new explicit codec
is a prerequisite for ONE uniform CK_A(u), not a separate fixed point chosen
independently for each literal sentence. No logical fixed point is asserted yet. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowParameterSelfApplication
open GorbowSyntax GorbowSortedSyntaxCode

def openDictionary (phi : Formula 2) : Fin 2 → Term 1 :=
  Fin.cases (Term.numeral (formulaCode phi)) (fun _ => .var 0)

def openSelf (phi : Formula 2) : Formula 1 :=
  GorbowFormulaSubstitution.substituteFormula (openDictionary phi) phi

def closedDictionary (phi : Formula 2) (u : Nat) : Fin 2 → Term 0 :=
  Fin.cases (Term.numeral (formulaCode phi)) (fun _ => Term.numeral u)

def closedSelf (phi : Formula 2) (u : Nat) : Sentence :=
  GorbowFormulaSubstitution.substituteFormula (closedDictionary phi u) phi

def rawParameterSelf (raw : List Nat) (u : Nat) : Option (List Nat) :=
  GorbowSubstitutionCode.substituteFormulaCode 2 0
    [GorbowCodeConstructors.numeral (formulaRawNumber raw),
      GorbowCodeConstructors.numeral u] raw

def numeric (code u : Nat) : Option Nat := do
  let raw ← decodeFormulaRaw code
  let out ← rawParameterSelf raw u
  pure (formulaRawNumber out)

end LogicLineages.ComputabilityKnowledge.GorbowParameterSelfApplication
