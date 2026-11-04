module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.Targets

/-- The proposed principal-start, original-schedule process equals the existing
companion process. Equality is a conclusion, not a convention field/premise. -/
def SourceProcessBridge : Prop := ∀ d c t : Nat, 1 ≤ d → c+d+1 ≤ t →
  sourceCount d c t = actualSuffixKernelCount (Ordinal.omega0 ^ (d : Ordinal)) c t ∧
  sourceValue d c t = actualSuffixKernel (Ordinal.omega0 ^ (d : Ordinal)) c t ∧
  (∀ i : Nat, 1 ≤ i → i ≤ sourceCount d c t →
    sourceState d c t i = actualControlledStateAfter (compensatedPrefixControl c)
      (actualSuffixKernelInitial (Ordinal.omega0 ^ (d : Ordinal)) c t) i) ∧
  0 < sourceCount d c t ∧
  sourceState d c t (sourceCount d c t) < Ordinal.omega0 ∧
  (∀ i : Nat, i < sourceCount d c t → Ordinal.omega0 ≤ sourceState d c t i) ∧
  (∀ i : Nat, 1 ≤ i → i ≤ sourceCount d c t →
    c + actualOrdinalNorm (sourceState d c t i) = (Phi^[i]) t)

/-- Exact proposed signed domain, with its explicit effective tail. The
degree-one negative obstruction remains a required, positive output clause. -/
def SignedDomainContract : Prop :=
  (∀ c t : Nat, c+2 ≤ t → ∀ j : Int,
    signedKernelDepth 1 c j t = 1+j ∧
      (0 < signedKernelDepth 1 c j t ↔ 0 ≤ j)) ∧
  (∀ c : Nat, ∀ j : Int, j < 0 →
    ¬ ∃ T : Nat, ∀ t : Nat, T ≤ t → c+2 ≤ t → 0 < signedKernelDepth 1 c j t) ∧
  (∀ d c : Nat, ∀ j : Int, admissibleSignedPair d j → ∀ t : Nat,
    correctedSignedKernelThreshold d c j 1 ≤ t → 0 < signedKernelDepth d c j t)

/-- Source-shaped exact block lemma AFTER the proposed convention/domain
correction. Actual numeric functions are identified with the independently
defined source process by SourceProcessBridge, rather than redefined here. -/
def CorrectedKernelRecursion : Prop :=
  (∀ c t : Nat, c+2 ≤ t →
    actualSuffixKernelCount Ordinal.omega0 c t = 1 ∧
      actualSuffixKernel Ordinal.omega0 c t = Phi t) ∧
  (∀ c t : Nat, c+3 ≤ t →
    actualSuffixKernelCount (Ordinal.omega0 ^ (2 : Ordinal)) c t =
      Phi t / 2 - (c+1)/2 + 1) ∧
  (∀ n c t : Nat, c+2*(n+2)+1 ≤ t →
    let parent := Ordinal.omega0 ^ ((n+2 : Nat) : Ordinal)
    let child := Ordinal.omega0 ^ ((n+1 : Nat) : Ordinal)
    let entry := actualSuffixKernel parent (c+n+2) t
    actualSuffixKernelCount parent c t = actualSuffixKernelCount child c entry +
      actualSuffixKernelCount parent (c+n+2) t ∧
    actualSuffixKernel parent c t = actualSuffixKernel child c entry) ∧
  (∀ n c : Nat, ∀ j : Int, (1 ≤ n ∨ 0 ≤ j) → ∀ t : Nat,
    finiteKernelRecursionThreshold (n+2) c j ≤ t →
    let entry := actualSuffixKernel (Ordinal.omega0 ^ ((n+2 : Nat) : Ordinal)) (c+n+2) t
    0 < signedKernelDepth (n+2) c j t ∧ 0 < signedKernelDepth (n+1) c j entry ∧
    rawSignedKernelValue (n+2) c j t = rawSignedKernelValue (n+1) c j entry) ∧
  (∀ c t : Nat, c+3 ≤ t → ∀ j : Int,
    signedKernelDepth 2 c j t = ((Phi t / 2 : Nat) : Int) +
      (j - (((c+1)/2 : Nat) : Int)) + 1 ∧
    rawSignedKernelValue 2 c j t = rawQuadraticShift (j - (((c+1)/2 : Nat) : Int)) t) ∧
  Computable (fun p : Nat × Nat × Nat => encodedFiniteKernelCount p.1 p.2.1 p.2.2) ∧
  Computable (fun p : Nat × Nat × Nat => encodedFiniteKernelValue p.1 p.2.1 p.2.2) ∧
  (∀ d c t : Nat, 1 ≤ d → c+d+1 ≤ t →
    encodedFiniteKernelCount d c t = actualSuffixKernelCount (Ordinal.omega0 ^ (d : Ordinal)) c t ∧
    encodedFiniteKernelValue d c t = actualSuffixKernel (Ordinal.omega0 ^ (d : Ordinal)) c t)

/-- Both the displayed partition formula and computed residues, with one
explicit tail and genuine signed depths. Counts use the independent source
schedule directly. No oracle supplies a residue, cutoff or process equality. -/
def CorrectedKernelResidues : Prop :=
  (∀ d c : Nat, ∀ j : Int, admissibleSignedPair d j → ∀ m : Nat, 1 ≤ m →
    ∀ t : Nat, residueTail d c j m ≤ t →
      0 < signedKernelDepth d c j t ∧
      Nat.ModEq m (rawSignedKernelValue d c j t) (fastControlResidue m) ∧
      Nat.ModEq m (sourceCount d c t)
        (restrictedPartitionCount d (kernelModularDifference (restrictedPartitionPeriod d m)
          (fastControlResidue (restrictedPartitionPeriod d m)) c)) ∧
      kernelCounterResidue d c m < m ∧
      sourceCount d c t % m = kernelCounterResidue d c m) ∧
  Primrec (fun z : Nat × Nat × Nat => kernelCounterResidue z.1 z.2.1 z.2.2) ∧
  (∀ j : Int, Primrec (fun z : Nat × Nat × Nat => residueTail z.1 z.2.1 j z.2.2))

open CounterLeaderExpansion CounterLeaderCollision

/-- The complete all-rank>=3 counter package, with every printed clause and
uniform effective tail maps; no convention or collision conclusion is assumed. -/
def CorrectedCounterSource : Prop :=
  (∀ n m c e t u : Nat,
    CounterSourceTheorem.commonTail n m c e ≤ t →
    CounterSourceTheorem.commonTail n m c e ≤ u →
    (entries n c t).map Prod.fst = (List.range (n+1)).reverse.map (fun i => i+3) ∧
    Even (leader n c t) ∧
    (count (n+3) c t : Int) = (leader n c t / 2 : Nat) + 1 - ((c+1)/2 : Nat) +
      ((residuals n c t).sum : Int) ∧
    leader n c t < 2 * count (n+3) c t ∧
    4 * count (n+3) c t < 3 * leader n c t ∧
    (leader n c t = leader m e u → c = e) ∧
    (m ≤ n → leader n c t = leader m e u →
      u = alignedInput (n-m) m c t ∧
      (count (n+3) c t : Int) - (count (m+3) e u : Int) =
        ((upperResiduals (n-m) m c t).sum : Int) ∧
      (∀ p ∈ upperEntries (n-m) m c t, m+3 < p.1) ∧
      (m < n → count (m+3) e u < count (n+3) c t)) ∧
    (count (n+3) c t < count (m+3) e u ↔
      leader n c t < leader m e u ∨ (leader n c t = leader m e u ∧ n < m)) ∧
    (count (n+3) c t = count (m+3) e u ↔ leader n c t = leader m e u ∧ n = m)) ∧
  Primrec (fun p : Nat × Nat × Nat × Nat =>
    CounterSourceTheorem.commonTail p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat × Nat =>
    CounterResidualDivergence.threshold p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat × Nat =>
    CounterFixedShiftComparison.threshold p.1 p.2.1 p.2.2.1 p.2.2.2)

end LogicLineages.OrdinalComparison.KernelSourceCompletion.Targets
