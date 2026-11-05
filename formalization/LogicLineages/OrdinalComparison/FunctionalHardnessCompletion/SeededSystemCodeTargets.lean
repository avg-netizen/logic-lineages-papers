module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSystemCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSystemCode.Targets
open OriginalDomain FunctionalDetector

def ExactDetectorCode : Prop := ∀ (Γ : List Ty) (a b : OriginalTerm Γ unary),
  detectorCode (SyntaxCode.encodeTerm a, SyntaxCode.encodeTerm b) =
    SourceGammaAggregateCode.pairCode
      (left (alignedLeft a) (alignedRight b), right (alignedLeft a) (alignedRight b))

/-- Literal context and original-name embedding. Two fresh witnesses are added
per equation; none of the original shared unknowns are duplicated or dropped. -/
def ExactContextAndEmbedding : Prop := ∀ (n : Nat) (s : System n),
  (SeededSystem.compile s).context = List.replicate (2 * s.length) .ground ++ SignedPair.Context n ∧
  ∀ (τ : Ty) (x : Variable (SignedPair.Context n) τ),
    SourceTypedPorts.variableIndex ((SeededSystem.compile s).original x) =
      SourceTypedPorts.variableIndex x + 2 * s.length

def ExactSystemCode : Prop := ∀ (n : Nat) (s : System n),
  systemCode n (s.map SeededSourceCode.expressionCode) =
    (2 * s.length, (SeededSystem.compile s).detectors.map SourceGammaAggregateCode.pairCode)

def ExactQueryPairs : Prop := ∀ (n : Nat) (s : System n),
  strictCode n (s.map SeededSourceCode.expressionCode) =
    SourceGammaAggregateCode.pairCode (SeededSystem.strictPair s) ∧
  weakCode n (s.map SeededSourceCode.expressionCode) =
    SourceGammaAggregateCode.pairCode (SeededSystem.weakPair s) ∧
  contextCode n (s.map SeededSourceCode.expressionCode) =
    (SeededSystem.compile s).context.map SyntaxCode.typeCode

/-- Total numerical programs for every raw row list. The exact semantic claims
above refer to the actual typed systems, not arbitrary malformed rows. -/
def NumericalPrograms : Prop :=
  Primrec₂ alignCode ∧ Primrec₂ payloadCode ∧ Primrec₂ leftCode ∧ Primrec₂ rightCode ∧
  Primrec detectorCode ∧ Primrec (fun p : Nat × Nat × State => step p.1 p.2.1 p.2.2) ∧
  Primrec₂ systemCode ∧ Primrec₂ strictCode ∧ Primrec₂ weakCode ∧ Primrec₂ contextCode

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSystemCode.Targets
