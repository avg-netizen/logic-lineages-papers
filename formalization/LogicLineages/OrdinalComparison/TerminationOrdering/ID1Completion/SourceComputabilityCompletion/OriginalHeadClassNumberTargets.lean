module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHeadClassNumberDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHeadClassNumberTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (suc z)
/-- Native calibration on actual original numbered heads only. -/
def NativeCalibration : Prop := ∀ (n : Nat) (h : NumberedAuxiliaryCoding.HeadCode (Fin n)),
  evaluate OriginalHeadClassNumber.classNumber
    (NumberedLeastCodeRepresentative.headNumber h ::ᵥ List.Vector.nil) =
      NumberedExchangeGuardsPrimrecProof.headClassNumber h
/-- Independent internal literal cases, including unknown-tag fallback.
No decoded/source/native/finite-window premise. -/
def LiteralCases : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (tag : Nat) (raw payload : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 InternalPairing.pairing raw (numeral tag) payload).imp
      (graph1 OriginalHeadClassNumber.classNumber
        (if tag = 4 then suc z else if tag = 5 then suc (suc payload) else z) raw)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHeadClassNumberTargets
