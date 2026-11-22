module
public import LogicLineages.PermittedControl.ActualZeroEdgeAlphabetCodeTargets
public import LogicLineages.PermittedControl.ActualSyntaxChargeBudgetTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualEffectiveGlobalTail
open OrdinalComparison PreparedProjection MixedSameRankResidue
open ActualZeroClassCommonTail ActualZeroEdgeAlphabetCode ActualZeroEdgeAlphabet
open ActualNodeTailSupply ActualFiniteGlobalTail ActualSyntaxChargeBudget ConcreteCountPairReplacement

def prefixAffordabilityCode (B : Nat) (p : PrefixCode) : Nat :=
  max (rawNormCode p.2.1) (max (rawNormCode p.2.2 + 3) (max 1 B))

/-- Keep the unfactored original safe max in P-versus-Q order:
higher source P first, candidate lower anchor Q second. -/
def pairTailCode (B : Nat) (lower higher : PrefixCode) : Nat :=
  safeTailCode (higher.2,lower.2) B

def labelsTailCode (B : Nat) (labels : List PrefixCode) : Nat :=
  max (finiteMax (prefixAffordabilityCode B) labels)
    (finiteMax (fun lower => finiteMax (pairTailCode B lower) labels) labels)

def alphabetTailCode (B : Nat) (alphabet : AlphabetCode) : Nat :=
  max (finiteMax annotationBoundCode alphabet) (labelsTailCode B (prefixChoicesCode alphabet))

def suppliedTailCode (B budget : Nat) (alphabet : AlphabetCode) : Nat :=
  alphabetTailCode B (collectCode budget alphabet)

/-- Uses the proved sufficient upper budget, not the exact signed
charge. The program does not validate malformed raw syntax. -/
def inputTailCode (B r : Nat) (terms : List WeightedCode) : Nat :=
  suppliedTailCode B (syntaxBudgetCode r terms) (terms.map Prod.snd)

def CodeEffectivity : Prop :=
  Primrec₂ alphabetTailCode ∧
  Primrec (fun p : Nat × Nat × AlphabetCode => suppliedTailCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × List WeightedCode => inputTailCode p.1 p.2.1 p.2.2)

def CodeCalibration : Prop :=
  (∀ (B : Nat) (alphabet : List LowerOperand),
    alphabetTailCode B (alphabet.map LowerOperand.code) = alphabetTail B alphabet) ∧
  (∀ (B budget : Nat) (alphabet : List LowerOperand),
    suppliedTailCode B budget (alphabet.map LowerOperand.code) =
      alphabetTail B ((List.range (budget+1)).flatMap (fun d => expandSteps d alphabet))) ∧
  ∀ (B r : Nat) (terms : List WeightedOperand),
    inputTailCode B r (terms.map encodeWeighted) =
      alphabetTail B ((List.range (syntaxBudget r terms+1)).flatMap
        (fun d => expandSteps d (terms.map Prod.snd)))

/-- Actual input-rank payment remains a hypothesis. The separate
nonzero terminal sign cutoff is not included in this bound. -/
def ExactTailDominance : Prop :=
  (∀ (B r : Nat) (terms : List WeightedOperand),
    globalTail B r terms ≤ inputTailCode B r (terms.map encodeWeighted)) ∧
  ∀ (B r : Nat) (ρ : Nat → Nat) (terms : List WeightedOperand),
    (∀ t ∈ terms, inputTailCode B r (terms.map encodeWeighted) ≤ ρ t.2.rank) →
    PaidGlobalTail B r ρ terms

def FullActualEffectiveGlobalTail : Prop :=
  CodeEffectivity ∧ CodeCalibration ∧ ExactTailDominance

end LogicLineages.PermittedControl.ActualEffectiveGlobalTail
