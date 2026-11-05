module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.PlainSystemCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.PlainSystemCode.Targets
open SignedPair

/-- The existing numeric program agrees with the PLAIN compiler at its actual
n-variable type, without any seed substitution or extra free variable. -/
def ExactPlainCompiler : Prop := ∀ (n : Nat) (d : Expression n),
  SeededSourceCode.compilerCode n (SeededSourceCode.expressionCode d) =
    (SeededSourceCode.pairCode (SignedPair.compile d).pair, (SignedPair.compile d).exponent)

def ExactContextAndEmbedding : Prop := ∀ (n : Nat) (s : System n),
  (compileSystem s).context = List.replicate (2 * s.length) .ground ++ Context n ∧
  ∀ (τ : Ty) (x : Variable (Context n) τ),
    SourceTypedPorts.variableIndex ((compileSystem s).original x) =
      SourceTypedPorts.variableIndex x + 2 * s.length

def ExactSystemCode : Prop := ∀ (n : Nat) (s : System n),
  systemCode n (s.map SeededSourceCode.expressionCode) =
    (2 * s.length, (compileSystem s).detectors.map SourceGammaAggregateCode.pairCode)

/-- These are the existing plain source queries whose level-two bounds are
proved by SystemBoundProof, not the seeded level-three queries. -/
def ExactQueryPairs : Prop := ∀ (n : Nat) (s : System n),
  strictCode n (s.map SeededSourceCode.expressionCode) =
    SourceGammaAggregateCode.pairCode (strictSystemPair s) ∧
  weakCode n (s.map SeededSourceCode.expressionCode) =
    SourceGammaAggregateCode.pairCode (weakSystemPair s) ∧
  contextCode n (s.map SeededSourceCode.expressionCode) =
    (compileSystem s).context.map SyntaxCode.typeCode

def NumericalPrograms : Prop :=
  Primrec (fun p : Nat × Nat × State => step p.1 p.2.1 p.2.2) ∧
  Primrec₂ systemCode ∧ Primrec₂ strictCode ∧ Primrec₂ weakCode ∧ Primrec₂ contextCode

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.PlainSystemCode.Targets
