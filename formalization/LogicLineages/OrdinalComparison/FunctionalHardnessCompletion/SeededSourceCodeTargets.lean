module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSourceCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSourceCode.Targets
open OriginalDomain SignedPair FunctionalDetector

/-- Literal capture-avoiding source-code equations in the established radix-eight
codec. All source contexts and all actual typed input trees are retained. -/
def ExactCombinators : Prop := ∀ (Γ : List Ty) (a b : OriginalTerm Γ unary)
    (p q : Pair Γ) (d : Nat),
  combineCode (SyntaxCode.encodeTerm a) (SyntaxCode.encodeTerm b) =
    SyntaxCode.encodeTerm (combine a b) ∧
  projectCode (SyntaxCode.encodeTerm a) (SyntaxCode.encodeTerm b) =
    SyntaxCode.encodeTerm (project a b) ∧
  omegaCode (SyntaxCode.encodeTerm a) = SyntaxCode.encodeTerm (liftOmega a) ∧
  joinCode (pairCode p) (pairCode q) = pairCode (join p q) ∧
  padCode d (pairCode p) = pairCode (pad d p)

/-- Every original variable and BOTH fixed closed base pairs use exactly the
same source encoding as the accepted typed definitions, with no free seed. -/
def ExactLeaves : Prop :=
  (∀ Γ : List Ty, unitCode = pairCode (@unitPair Γ) ∧
    seedCode = pairCode (@OmegaSeed.pair Γ)) ∧
  (∀ (n : Nat) (i : Fin n), variableCode i.val = pairCode (variablePair i))

/-- No assumed numerical supplier: compilerCode is the explicit total
algorithm. It returns exactly the existing unfolded source pair AND scale. -/
def ExactCompilerCalibration : Prop :=
  ∀ (n : Nat) (d : Expression (n + 1)),
    compilerCode n (expressionCode d) =
      (pairCode (SeededCompiler.compile d).pair, (SeededCompiler.compile d).exponent)

/-- Actual primitive recursiveness on ALL raw natural inputs, including
malformed expressions and out-of-range variable indices. No semantics for
malformed codes, polynomial-system reduction or undecidability is asserted. -/
def NumericalPrograms : Prop :=
  Primrec₂ combineCode ∧ Primrec₂ projectCode ∧ Primrec omegaCode ∧
  Primrec₂ joinCode ∧ Primrec₂ padCode ∧ Primrec variableCode ∧ Primrec₂ compilerCode

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSourceCode.Targets
