module
public import LogicLineages.PermittedControl.ActualFiniteFullValueGuardsTargets
public import LogicLineages.PermittedControl.ActualSyntaxChargeBudgetTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualGlobalComparisonCeiling
open OrdinalComparison FieldComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand)
open ActualFullValueLabels (Label operandLabel labels)
open ActualFiniteFullValueGuards (familyCost ReadyFamily PaidFamily)
open ActualFiniteGlobalTail (syntaxOf globalAlphabet PaidGlobalTail LongState)
open ActualZeroEdgeAlphabet (expandSteps)
open ActualSyntaxChargeBudget (syntaxBudget)
open ActualReadChargeIteration (ReadState Trace ActiveAt NodeGuards)
open ActualZeroClassReplacement (Read liftedReads)
open ActualWeightedReadNormalization (normalizeReads)

def alphabetLabels (ops : List LowerOperand) : List Label := ops.filterMap operandLabel

def onAlphabet (B : Nat) (ops : List LowerOperand) : Nat := familyCost B (alphabetLabels ops)

noncomputable def budgetAlphabet (depth : Nat) (ts : List WeightedOperand) : List LowerOperand :=
  (List.range (depth+1)).flatMap (fun n => expandSteps n (ts.map Prod.snd))

/-- One finite syntax-derived comparison cost over every ordered label
pair in the sufficient source alphabet; impossible candidates are not
asserted to be real fields. -/
noncomputable def comparisonCeiling (B r : Nat) (ts : List WeightedOperand) : Nat :=
  onAlphabet B (budgetAlphabet (syntaxBudget r ts) ts)

def PaidComparisonCeiling (B r : Nat) (ρ : Nat → Nat) (ts : List WeightedOperand) : Prop :=
  ∀ t ∈ ts, comparisonCeiling B r ts ≤ ρ t.2.rank

def ExactAlphabetComparisonDominance : Prop :=
  (∀ (B : Nat) (ts : List WeightedOperand) (alphabet : List LowerOperand),
    (∀ t ∈ ts, t.2 ∈ alphabet) → familyCost B (labels ts) ≤ onAlphabet B alphabet) ∧
  ∀ (B r : Nat) (ts : List WeightedOperand),
    onAlphabet B (globalAlphabet r ts) ≤ comparisonCeiling B r ts

/-- The read state and reachability are genuine, not an arbitrary
symbolic tree. An actual active highest occurrence pays the greatest
bound at an original active rank; no empty-source top payment is
invented. Lower baseline values may agree only below that rank. -/
def ExactReachedComparisonFamily : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ baseline : Nat → Nat) (r top n : Nat) (initial reached : ReadState),
    StrictMono ρ → (∀ i : Nat, i < top → baseline i = ρ i) →
    liftedReads f ρ initial.reads →
    (∀ t ∈ syntaxOf initial, t.2.rank ≤ top) →
    PaidComparisonCeiling B r ρ (syntaxOf initial) →
    Trace f B ρ r top n initial reached →
    ∀ xs : List Read, normalizeReads f ρ reached.reads = some xs → ActiveAt top xs →
      NodeGuards B ρ xs →
      let ls := labels (xs.map Prod.fst)
      ReadyFamily B baseline top ls ∧ PaidFamily B baseline top (ρ top) ls

def ExactCombinedReachedComparisonSupply : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ baseline : Nat → Nat) (r top n : Nat) (initial reached : ReadState),
    StrictMono ρ → (∀ i : Nat, i < top → baseline i = ρ i) →
    liftedReads f ρ initial.reads → LongState initial →
    (∀ t ∈ syntaxOf initial, t.2.rank ≤ top) →
    PaidGlobalTail B r ρ (syntaxOf initial) →
    PaidComparisonCeiling B r ρ (syntaxOf initial) →
    Trace f B ρ r top n initial reached →
    ∀ xs : List Read, normalizeReads f ρ reached.reads = some xs → ActiveAt top xs →
      let ls := labels (xs.map Prod.fst)
      NodeGuards B ρ xs ∧ ReadyFamily B baseline top ls ∧ PaidFamily B baseline top (ρ top) ls

def FullActualGlobalComparisonCeiling : Prop :=
  ExactAlphabetComparisonDominance ∧ ExactReachedComparisonFamily ∧ ExactCombinedReachedComparisonSupply

end LogicLineages.PermittedControl.ActualGlobalComparisonCeiling
