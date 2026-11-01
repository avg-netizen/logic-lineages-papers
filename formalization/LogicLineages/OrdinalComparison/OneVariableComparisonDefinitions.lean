module
public import LogicLineages.OrdinalComparison.EncodedKernelWordDefinitions
public import LogicLineages.OrdinalComparison.PositiveInputPlugDefinitions
public import LogicLineages.OrdinalComparison.RawNormCodeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Literal section8 language: P1, or a finite kernel word on ONE open P1
argument. No sum of range expressions is inserted into a kernel argument. -/
inductive OneVariableComparisonExpr where
  | positive : FixedLimitPositiveExpr → OneVariableComparisonExpr
  | range : List (NONote × Nat) → FixedLimitPositiveExpr → OneVariableComparisonExpr

def comparisonRawWord (w : List (NONote × Nat)) : List (ONote × Nat) :=
  w.map (fun p => (p.1.1,p.2))

def oneVariableComparisonValid : OneVariableComparisonExpr → Prop
  | .positive E => fixedLimitProfileBelow epsilonZero E
  | .range w E => w≠[] ∧ (∀ p∈w, 0<p.1.1.repr) ∧
      fixedLimitProfileBelow epsilonZero E ∧ positiveExprHasInput E=true

noncomputable def actualOneVariableComparisonValue : OneVariableComparisonExpr → Nat → Nat
  | .positive E, x => actualFixedLimitProfileEval E x
  | .range w E, x => (actualPrincipalWordRun (comparisonRawWord w)
      (actualFixedLimitProfileEval E x)).1

noncomputable def oneVariableComparisonDomainAt : OneVariableComparisonExpr → Nat → Prop
  | .positive _, _ => True
  | .range w E, x => actualPrincipalWordGenuine (comparisonRawWord w)
      (actualFixedLimitProfileEval E x)

/-- Every dynamically reached input exceeds this same fixed syntax bound. -/
def comparisonWordDomainBound : List (NONote × Nat) → Nat
  | [] => 1
  | (eta,c)::rest => max (c+1+Vendor.R1.treeWeight eta.1) (comparisonWordDomainBound rest)

def oneVariableComparisonDomainBound : OneVariableComparisonExpr → Nat
  | .positive _ => 1
  | .range w _ => comparisonWordDomainBound w

def oneVariableComparisonEncode : OneVariableComparisonExpr → Nat
  | .positive E => 2*positiveExprEncode E
  | .range w E => 2*Nat.pair (Encodable.encode (encodePrincipalKernelWord (comparisonRawWord w)))
      (positiveExprEncode E)+1

def encodedComparisonWordDomainBound : List (Nat × Nat) → Nat
  | [] => 1
  | (eta,c)::rest => max (c+1+rawNormCode eta) (encodedComparisonWordDomainBound rest)

def encodedOneVariableComparisonDomainBound (n : Nat) : Nat :=
  if n%2=0 then 1 else
    encodedComparisonWordDomainBound
      ((Encodable.decode (α := List (Nat × Nat)) (n/2).unpair.1).getD [])

/-- Actual total numeric evaluator, preserving the original positive source
tree and the literal executable kernel word; late domain correctness is owed. -/
noncomputable def encodedOneVariableComparisonValue (n x : Nat) : Nat :=
  if n%2=0 then encodedPositiveEvaluation (n/2) x else
    let p := (n/2).unpair
    (encodedKernelWordRun ((Encodable.decode (α := List (Nat × Nat)) p.1).getD [])
      (encodedPositiveEvaluation p.2 x)).1

end LogicLineages.OrdinalComparison
