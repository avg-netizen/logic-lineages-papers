module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentCandidate.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentCandidate.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership
open InternalOriginalUniformParameterLeaves

/-- ORIGINAL all-vector candidate decoding, including failed context/Object
and packed decoding. Zero remains an ordinary raw value, not an Option tag. -/
def OriginalReencoding : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 2),
  candidateValue n arity v = if targetValue n arity v = 1 then v.get 0 else 0

/-- A concrete AST replaces only the opaque D witness. The original T and its
actual H/G calibration are unchanged; no internal conclusion is inferred. -/
def CalibratedCandidate : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (H G : Program 1),
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  CandidateCalibrated n arity (candidate (OriginalTypedDecoder.target H G))

/-- Accepted target graph gives arbitrary-output equality with the SAME input. -/
def AcceptedGraph : Prop := ∀ (T : Program 2) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (input parameter out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 T (numeral 1) input parameter)) →
  (Nonempty (Derivation body Delta (graph2 (candidate T) out input parameter)) ↔
   Nonempty (Derivation body Delta (equal out input)))

/-- Actual rejection keeps the literal zero fallback at arbitrary runtime inputs. -/
def RejectedGraph : Prop := ∀ (T : Program 2) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (input parameter out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 T (numeral 0) input parameter)) →
  (Nonempty (Derivation body Delta (graph2 (candidate T) out input parameter)) ↔
   Nonempty (Derivation body Delta (equal out (numeral 0))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentCandidate.Targets
