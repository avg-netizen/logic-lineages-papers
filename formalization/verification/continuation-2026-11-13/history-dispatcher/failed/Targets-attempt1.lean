module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector

/-- Construct all actual history-independent leaves. Calibrations are external,
all-vector statements; they are never reflected into internal arithmetic. -/
def ConstructLeaves : Prop := ∃ (valid logical arithmetic : Program 1) (axiom : Program 3),
  NativeLeaves valid logical arithmetic axiom

/-- Original full theory lineCheck, every Line including malformed payloads.
This is not yet arbitrary encoded/default state calibration for the kernel. -/
def NativeLineDispatcher : Prop := ∀ (valid logical arithmetic : Program 1) (axiom : Program 3),
  NativeLeaves valid logical arithmetic axiom →
  ∀ index fuel (h : GorbowProofChecker.History) (l : GorbowProofChecker.Line),
  evaluate (lineDispatcher valid logical arithmetic axiom)
    (index ::ᵥ fuel ::ᵥ Encodable.encode h ::ᵥ Encodable.encode l ::ᵥ nil) =
  truth (GorbowTheoryChecker.lineCheck
    (GorbowEnumeratedProvability.axiomCheck (Denumerable.ofNat GorbowEnumeratedProvability.Code index,fuel)) h l)

/-- Actual whole dispatcher suffix acceptance. No native calibration hypothesis
is needed: the selected leaf calls are unchanged because they do not read
history. The formula retains arbitrary line/source terms and malformed guards. -/
def InternalLineSuffix : Prop := ∀ (valid logical arithmetic : Program 1) (axiom : Program 3),
  ∀ arity (p : Program arity) tag appendTag,
  (nodes p)[tag]? = some ⟨4,lineDispatcher valid logical arithmetic axiom⟩ →
  (nodes p)[appendTag]? = some ⟨2,HistoryAppend.append⟩ →
  ∀ ctx (index fuel h tail line : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (.equal (dispatcherCall tag index fuel h line) (.succ .zero))
      (.equal (dispatcherCall tag index fuel (HistoryAppend.appendCall appendTag h tail) line) (.succ .zero))))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.Targets
