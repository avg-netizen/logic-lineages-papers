module
public import LogicLineages.PermittedControl.ActualRawCanonicalZeroPrefixesTargets
public import LogicLineages.PermittedControl.ActualCanonicalStoppingTraceTargets
public import LogicLineages.PermittedControl.ActualSyntaxChargeBudgetTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalZeroTraceInclusion
open ActualRawSignedStaticCeiling (encodeSyntax)
open ActualRawCanonicalZeroReplay (encodeAnswers stepCode)
open ActualRawCanonicalZeroPrefixes (CandidatePath available prefixes)
open ActualCanonicalZeroTrace (CanonicalZeroWitness CanonicalTrace eraseState)
open ActualCanonicalStoppingTrace (StopsAt)
open ActualReadChargeIteration (ReadState RankBound stateCharge)
open ActualFiniteGlobalTail (LongState syntaxOf PaidGlobalTail)
open ActualGlobalComparisonCeiling (PaidComparisonCeiling)
open ActualSyntaxChargeBudget (syntaxBudgetCode)
open ActualZeroClassReplacement (liftedReads)
open ActualFullLabelPairGuards (Answer)

def entry (answers : List (List Answer)) (out : ReadState) :
    ActualRawCanonicalZeroPrefixes.Candidate :=
  (encodeAnswers answers,encodeSyntax (eraseState out))

def ExactActualZeroCandidateEdge : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (r top : Nat) (source target : ReadState) (answer : List Answer),
    CanonicalZeroWitness f B ρ r top source target answer →
      answer.map Answer.code ∈ available (encodeSyntax (eraseState source)) ∧
      stepCode (encodeSyntax (eraseState source),answer.map Answer.code) =
        some (encodeSyntax (eraseState target))

def ExactActualCanonicalCandidateTrace : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (r top : Nat) (source target : ReadState) (answers : List (List Answer)),
    CanonicalTrace f B ρ r top answers source target →
      CandidatePath (encodeSyntax (eraseState source)) (encodeAnswers answers)
        (encodeSyntax (eraseState target)) ∧
      entry answers target ∈ prefixes (stateCharge r source) (encodeSyntax (eraseState source))

/-- Computable upper budget as well as the exact typed fuel. This does
not infer any typed trace or correctness of any other candidate. -/
def ExactActualCanonicalBudgetInclusion : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (r top : Nat) (source target : ReadState) (answers : List (List Answer)),
    CanonicalTrace f B ρ r top answers source target →
      let raw := encodeSyntax (eraseState source)
      entry answers target ∈ prefixes (syntaxBudgetCode r raw.2) raw

def ExactFundedStoppingCandidateInclusion : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (r top : Nat) (source : ReadState),
    liftedReads f ρ source.reads → RankBound r top source → LongState source →
    PaidGlobalTail B r ρ (syntaxOf source) → PaidComparisonCeiling B r ρ (syntaxOf source) →
    ∃ (answers : List (List Answer)) (target : ReadState),
      CanonicalTrace f B ρ r top answers source target ∧ StopsAt f B ρ r top target ∧
      (let raw := encodeSyntax (eraseState source)
       entry answers target ∈ prefixes (syntaxBudgetCode r raw.2) raw)

def FullActualRawCanonicalZeroTraceInclusion : Prop :=
  ExactActualZeroCandidateEdge ∧ ExactActualCanonicalCandidateTrace ∧
    ExactActualCanonicalBudgetInclusion ∧ ExactFundedStoppingCandidateInclusion

end LogicLineages.PermittedControl.ActualRawCanonicalZeroTraceInclusion
