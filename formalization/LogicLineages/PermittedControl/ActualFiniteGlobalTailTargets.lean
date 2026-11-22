module
public import LogicLineages.PermittedControl.ActualZeroEdgeAlphabetTargets
public import LogicLineages.PermittedControl.ActualNodeTailSupplyTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFiniteGlobalTail
open PreparedProjection MixedSameRankResidue ActualZeroClassReplacement
open ActualReadChargeIteration ActualZeroEdgeAlphabet ActualNodeTailSupply
open ActualShortCountCleanup

def syntaxOf (s : ReadState) : List WeightedOperand := s.reads.map Prod.fst

/-- Dummy payloads are used only in computing the structural charge.
No actual read, hit or other semantic status is asserted about them. -/
noncomputable def syntaxCharge (r : Nat) (terms : List WeightedOperand) : Nat :=
  stateCharge r ⟨0,terms.map (fun t => (t,0))⟩

noncomputable def globalAlphabet (r : Nat) (terms : List WeightedOperand) : List LowerOperand :=
  (List.range (syntaxCharge r terms + 1)).flatMap (fun depth => expandSteps depth (terms.map Prod.snd))

def unitTerms (alphabet : List LowerOperand) : List WeightedOperand :=
  alphabet.map (fun op => (1,op))

noncomputable def alphabetTail (B : Nat) (alphabet : List LowerOperand) : Nat :=
  nodeTail B (unitTerms alphabet)

noncomputable def globalTail (B r : Nat) (terms : List WeightedOperand) : Nat :=
  alphabetTail B (globalAlphabet r terms)

/-- One explicit numerical payment at each original used rank, not
a theorem that an arbitrary valuation satisfies the bound. -/
def PaidGlobalTail (B r : Nat) (ρ : Nat → Nat) (terms : List WeightedOperand) : Prop :=
  ∀ t ∈ terms, globalTail B r terms ≤ ρ t.2.rank

def LongState (s : ReadState) : Prop := ∀ rd ∈ s.reads, LongCountOperand rd.1.2

def ExactSyntaxCharge : Prop :=
  ∀ (r : Nat) (s : ReadState), syntaxCharge r (syntaxOf s) = stateCharge r s

def ExactGlobalLabelEnclosure : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r zRank n : Nat) (initial reached : ReadState),
    Trace f B ρ r zRank n initial reached → Covers (globalAlphabet r (syntaxOf initial)) reached

def ExactAlphabetTailDominance : Prop :=
  ∀ (B : Nat) (terms : List WeightedOperand) (alphabet : List LowerOperand),
    (∀ t ∈ terms, t.2 ∈ alphabet) → nodeTail B terms ≤ alphabetTail B alphabet

/-- Discharge the fixed-valuation iteration's local reached-node
numerical supply from one finite tail payment on the original syntax.
The initial long shape is genuine, and later shape is derived. -/
def ExactGlobalGuardSupply : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r zRank : Nat) (initial : ReadState),
    liftedReads f ρ initial.reads → LongState initial →
    PaidGlobalTail B r ρ (syntaxOf initial) →
    ReachedGuardSupply f B ρ r zRank initial

def FullActualFiniteGlobalTail : Prop :=
  ExactSyntaxCharge ∧ ExactGlobalLabelEnclosure ∧
    ExactAlphabetTailDominance ∧ ExactGlobalGuardSupply

end LogicLineages.PermittedControl.ActualFiniteGlobalTail
