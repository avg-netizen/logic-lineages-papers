module
public import LogicLineages.PermittedControl.ActualReadChargeIterationTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroEdgeAlphabet
open PreparedProjection ActualZeroClassReplacement ActualZeroClassCommonTail
open ActualReadChargeIteration ConcreteCountPairReplacement

/-- A finite typed syntax list, not a list of verified actual counts.
Weight, control, valuation, class key and success are not consulted. -/
def prefixCandidates (alphabet : List LowerOperand) : List PrefixLabel :=
  alphabet.filterMap (fun op => prefixLabel (1,op))

def prefixOperand (l : PrefixLabel) : LowerOperand :=
  .count l.rank l.lam l.eta

/-- First argument is the potential lower anchor Q; second is the
higher original proper prefix P. No actual guard is asserted here. -/
noncomputable def pairOperand (lower higher : PrefixLabel) : LowerOperand :=
  replacementOperand lower.rank higher.lam higher.eta lower.lam lower.eta

noncomputable def pairCandidates (labels : List PrefixLabel) : List LowerOperand :=
  labels.flatMap (fun lower =>
    (labels.filter (fun higher => decide (lower.rank < higher.rank))).map (pairOperand lower))

noncomputable def expand (alphabet : List LowerOperand) : List LowerOperand :=
  let labels := prefixCandidates alphabet
  alphabet ++ (labels.map prefixOperand ++ pairCandidates labels)

noncomputable def expandSteps : Nat → List LowerOperand → List LowerOperand
  | 0, alphabet => alphabet
  | n+1, alphabet => expandSteps n (expand alphabet)

def Covers (alphabet : List LowerOperand) (s : ReadState) : Prop :=
  ∀ rd ∈ s.reads, rd.1.2 ∈ alphabet

/-- The finite list only overapproximates possible labels. Membership
may not imply a proper interval, actual collision, survival or hit. -/
def ExactZeroEdgeAlphabet : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r zRank : Nat)
    (source out : ReadState) (alphabet : List LowerOperand),
    ZeroEdge f B ρ r zRank source out → Covers alphabet source →
    Covers (expand alphabet) out

/-- The trace uses the exact actual-edge definition, not a supplied
syntactic transition relation. Each edge costs at least one unit. -/
def ExactTraceAlphabet : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r zRank n : Nat)
    (source out : ReadState), Trace f B ρ r zRank n source out →
    n + stateCharge r out ≤ stateCharge r source ∧
    ∀ alphabet : List LowerOperand, Covers alphabet source → Covers (expandSteps n alphabet) out

def FullActualZeroEdgeAlphabet : Prop := ExactZeroEdgeAlphabet ∧ ExactTraceAlphabet

end LogicLineages.PermittedControl.ActualZeroEdgeAlphabet
