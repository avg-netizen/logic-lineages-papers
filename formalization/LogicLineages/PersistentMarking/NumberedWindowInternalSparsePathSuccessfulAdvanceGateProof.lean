module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenCallsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenGateProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGateProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelope (hopGood hopTarget hopSource hopWitness hopRawTarget)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary hopCertified)
open NumberedWindowInternalSparsePathAdvance
open NumberedWindowInternalSparsePathAdvanceTargets
open NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof (coords atHopIntro)
open NumberedWindowInternalSparsePathAdvanceOpenChecks (exact_OpenAdvanceGate)
open NumberedWindowInternalSparsePathAdvanceOpenCallsProof (callsRead callsIntro)
open NumberedWindowInternalSparsePathAdvanceOpenGateProof (resultOfGate)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem atHopRead (p : Program 1) (out ctx ty initial hop : OTerm α)
    (known : Nonempty (Derivation body Γ (programGraph (atHop p) out (coords ctx ty initial hop)))) :
    Nonempty (Derivation body Γ (unary p out hop)) := by
  apply compositionRecover p (fun _ : Fin 1 => .projection 3) out (coords ctx ty initial hop)
    (![hop] : Fin 1 → OTerm α) known
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue (3 : Fin 4) (coords ctx ty initial hop)

private abbrev rawAndLeast (raw : Program 5) (least : Program 3) :=
  conjunction (rawCall raw) (conjunction (fromMatches least) (toMatches least))

private theorem readGood (raw : Program 5) (least : Program 3)
    (ctx ty initial hop : OTerm α)
    (good : Nonempty (Derivation body Γ (acceptedGuard raw least ctx ty initial hop))) :
    Nonempty (Derivation body Γ (unary hopGood (suc z) hop)) := by
  let xs := coords ctx ty initial hop
  let localGood := conjunction (atHop hopGood) (rawAndLeast raw least)
  obtain ⟨h⟩ := conjunctionRecover statePresent localGood xs good
  obtain ⟨g⟩ := conjunctionRecover (atHop hopGood) (rawAndLeast raw least) xs
    ⟨Derivation.conjunctionRight h⟩
  exact atHopRead hopGood (suc z) ctx ty initial hop ⟨Derivation.conjunctionLeft g⟩

theorem obtainCalls (raw : Program 5) (least : Program 3) (ctx ty current hop target q w r : OTerm α)
    (accepted : Nonempty (Derivation body Γ (selectedGraph raw least (suc target) ctx ty (suc current) hop)))
    (src : Nonempty (Derivation body Γ (unary hopSource q hop)))
    (wit : Nonempty (Derivation body Γ (unary hopWitness w hop)))
    (dst : Nonempty (Derivation body Γ (unary hopRawTarget r hop))) :
    Nonempty (Derivation body Γ (hopCalls raw least ctx ty current hop target q w r)) := by
  obtain ⟨gate⟩ := exact_OpenAdvanceGate body raw least α ctx ty (suc current) hop target
  obtain ⟨g⟩ := closedApply ⟨Derivation.conjunctionRight gate⟩ accepted
  have stamped : Nonempty (Derivation body Γ (acceptedGuard raw least ctx ty (suc current) hop)) :=
    ⟨Derivation.conjunctionLeft g⟩
  obtain ⟨tag⟩ := readGood raw least ctx ty (suc current) hop stamped
  obtain ⟨t⟩ := atHopRead hopTarget target ctx ty (suc current) hop ⟨Derivation.conjunctionRight g⟩
  obtain ⟨a⟩ := src
  obtain ⟨b⟩ := wit
  obtain ⟨c⟩ := dst
  have cert : Derivation body Γ (hopCertified hop target q w r) :=
    Derivation.conjunctionIntroduction tag (Derivation.conjunctionIntroduction t
      (Derivation.conjunctionIntroduction a (Derivation.conjunctionIntroduction b c)))
  obtain ⟨calls⟩ := callsRead raw least ctx ty current hop target q w r ⟨cert⟩ stamped
  exact ⟨Derivation.conjunctionIntroduction cert calls⟩

theorem acceptCalls (raw : Program 5) (least : Program 3) (ctx ty current hop target q w r : OTerm α)
    (read : Nonempty (Derivation body Γ (hopCalls raw least ctx ty current hop target q w r))) :
    Nonempty (Derivation body Γ (selectedGraph raw least (suc target) ctx ty (suc current) hop)) := by
  obtain ⟨all⟩ := read
  let cert := Derivation.conjunctionLeft all
  have guard := callsIntro raw least ctx ty current hop target q w r ⟨cert⟩
    ⟨Derivation.conjunctionRight all⟩
  have actual := atHopIntro hopTarget target ctx ty (suc current) hop
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cert)⟩
  exact resultOfGate raw least ctx ty (suc current) hop target guard actual

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGateProof
