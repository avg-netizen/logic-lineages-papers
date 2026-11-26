module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HistoryMachine.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HistoryMachine.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB List.Vector

/-- All four suppliers must be CONSTRUCTED, not assumed at the final tuple. -/
def NativePrograms : Prop :=
  ∃ (kernel : Program 3) (bound initial : Program 1) (finalizer : Program 4),
    KernelProgram kernel ∧ BoundProgram bound ∧ InitialProgram initial ∧ FinishProgram finalizer

def IteratorCalibration : Prop :=
  ∀ (kernel : Program 3), KernelProgram kernel →
  ∀ (state : State) index fuel count,
    evaluate (iterator kernel) (count ::ᵥ Encodable.encode state ::ᵥ index ::ᵥ fuel ::ᵥ nil) =
      Encodable.encode ((transition index fuel)^[count] state)

def OriginalHistoryRun : Prop :=
  ∀ (index fuel : Nat) (state : Option GorbowProofChecker.History)
      (lines : List GorbowProofChecker.Line) count,
    lines.length ≤ count →
    (transition index fuel)^[count] (state,lines) =
      ((lines.foldl (GorbowTheoryChecker.step
        (GorbowEnumeratedProvability.axiomCheck (Denumerable.ofNat Code index,fuel))) state),[])

def SameNumericChecker : Prop :=
  ∀ (kernel : Program 3) (bound initial : Program 1) (finalizer : Program 4),
    KernelProgram kernel → BoundProgram bound → InitialProgram initial → FinishProgram finalizer →
    UniversalVerifier (checker kernel bound initial finalizer)

def OpenFusion : Prop :=
  ∀ n (p : Program n) tag (kernel : Program 3),
    (nodes p)[tag]? = some ⟨4,iterator kernel⟩ →
  ∀ ctx (s state index fuel : Term ctx),
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.all (fusionTemplate tag s state index fuel)))

/-- The syntax-explicit checker and producer precede c/rho. Fuel's original
exact construction and ALL three internal fuel laws are retained at THIS same
actual tuple. The actual history-iteration recurrence has no oracle premise.
This is not the still-unpaid internal append/reference preservation theorem. -/
def SameSourceHistoryFusion : Prop :=
  ∃ (kernel : Program 3) (bound initial : Program 1) (finalizer : Program 4)
    (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
    (tagG : Nat) (pG : Program 6),
    KernelProgram kernel ∧ BoundProgram bound ∧ InitialProgram initial ∧ FinishProgram finalizer ∧
    UniversalVerifier (checker kernel bound initial finalizer) ∧
    Actual pF pR (Fuel.verifier (checker kernel bound initial finalizer)) c ∧
    SourceBaseCompletion.SyntaxAdequate pF pR (Fuel.verifier (checker kernel bound initial finalizer)) ∧
    GorbowUniformCommonKnowledge.CodeProgram pCK ∧
    GorbowUniformCommonKnowledge.RegistryInstall pF pR
      (Fuel.verifier (checker kernel bound initial finalizer)) tagCK pCK ∧
    GorbowUniformCommonKnowledge.FixedPointFor pF pR
      (Fuel.verifier (checker kernel bound initial finalizer)) c tagCK ∧
    InstalledProducer.ProducerFor (Fuel.verifier (checker kernel bound initial finalizer)) pG ∧
    InstalledProducer.RegistryInstall pF pR
      (Fuel.verifier (checker kernel bound initial finalizer)) tagG pG ∧
    Nonempty (Derivation (S pF pR (Fuel.verifier (checker kernel bound initial finalizer))) (Fuel.stepClause pF)) ∧
    Nonempty (Derivation (S pF pR (Fuel.verifier (checker kernel bound initial finalizer))) (Fuel.incrementClause pF)) ∧
    Nonempty (Derivation (S pF pR (Fuel.verifier (checker kernel bound initial finalizer))) (Fuel.monotonicityClause pF)) ∧
    Nonempty (Derivation (S pF pR (Fuel.verifier (checker kernel bound initial finalizer)))
      (fusionClause pF kernel bound initial finalizer))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HistoryMachine.Targets
