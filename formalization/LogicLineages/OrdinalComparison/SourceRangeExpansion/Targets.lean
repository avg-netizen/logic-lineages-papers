module
public import LogicLineages.OrdinalComparison.SourceRangeExpansion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceRangeExpansion.Targets
open PolynomialGraphCompletion WordGuardCompletion CounterWordGuardCompletion
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion

/-- Every emitted head belongs to the original finite-degree grammar; expansion
has two letters and no counters. Its extra length is not claimed to decrease. -/
def ExpansionSyntax : Prop := ∀ D n c : Nat, ∀ j : Int, n+3 ≤ D →
  WordAllowed D (expansionWord n c j) ∧ (expansionWord n c j).length = 2 ∧
  counterNodes (expansionWord n c j) = 0

/-- Original-source one-step signed recurrence, with parent and replacement
complete domains. Every companion bridge is proved at its genuine threshold. -/
def SourceBlockExpansion : Prop := ∀ D n c t : Nat, ∀ j : Int, n+3 ≤ D →
  expansionTail n c j ≤ t →
  LetterDomain (kernelLetter (n+3) c j) t ∧ WordDomain (expansionWord n c j) t ∧
  sourceSignedValue (n+3) c j t = wordValue (expansionWord n c j) t

/-- Replace a higher-rank head inside any original word context. Exact prefix
values transfer all outer domains, including signed shifts, without a fresh
variable, inverse counter or monotonicity assumption on the outer suffix. -/
def ContextExpansion : Prop := ∀ D : Nat, ∀ A S : Word, ∀ n c : Nat, ∀ j : Int,
  WordAllowed D A → WordAllowed D S → n+3 ≤ D → ∀ x : Nat,
  contextTail A S n c j ≤ x →
  WordAllowed D (A++expansionWord n c j++S) ∧
  WordDomain (A++[kernelLetter (n+3) c j]++S) x ∧
  WordDomain (A++expansionWord n c j++S) x ∧
  wordValue (A++[kernelLetter (n+3) c j]++S) x =
    wordValue (A++expansionWord n c j++S) x

/-- All actual syntax transformations and cutoffs are uniformly primitive
recursive, including arbitrary negative signed indices and both contexts. -/
def ExpansionPrograms : Prop :=
  Primrec (fun p : Nat × Nat × Int => lowerHead p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × Int => expansionWord p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × Int => expansionTail p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Word × Word × Nat × Nat × Int =>
    contextTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

end LogicLineages.OrdinalComparison.SourceRangeExpansion.Targets
