module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesRecursor.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesRecursor.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Original typed graph at every legal stage, with exact source-rank frontier.
No arbitrary supplier calibration or recursive correctness premise is assumed. -/
def OriginalGraph : Prop := ∀ (n : Nat) (seed : NumberedAuxiliaryCoding.Code (Fin n))
    (i param : Nat), i ≤ NumberedLeastCodeRepresentative.codeNumber seed + 1 →
  evaluate graph (List.Vector.ofFn ![i,NumberedLeastCodeRepresentative.codeNumber seed,param]) =
    NumberedMultisetNumeric.numbersNumber
      ((ArgumentEntriesFrontier.originalFrontier seed (NumberedLeastCodeRepresentative.codeNumber seed + 1 - i)).map
        (fun c => Nat.pair (NumberedLeastCodeRepresentative.codeNumber c)
          (Encodable.encode (NumberedExchangeCode.argumentEntries c))))
/-- Actual concrete literal nat_omega_rec' extraction, including malformed spines
represented by valid Code constructors (None versus Some [] preserved). -/
def OriginalExtraction : Prop := ∀ (n : Nat) (seed : NumberedAuxiliaryCoding.Code (Fin n)) (param : Nat),
  evaluate extract (List.Vector.ofFn ![NumberedLeastCodeRepresentative.codeNumber seed,param]) =
    Encodable.encode (NumberedExchangeCode.argumentEntries seed)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesRecursor.Targets
