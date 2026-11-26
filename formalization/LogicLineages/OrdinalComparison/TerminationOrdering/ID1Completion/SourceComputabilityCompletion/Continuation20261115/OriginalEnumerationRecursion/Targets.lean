module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- All numeric roots/parameters, without typed-image, codec-validity or
recursive-law assumptions. Calibration includes original final R+1 extraction. -/
def NativeNumeric : Prop := ∀ (n : Nat) (v : List.Vector Nat 2),
  evaluate (enumeration n) v = numeric n (Nat.unpair (v.get 0)).2 (Nat.unpair (v.get 0)).1 (v.get 1)
/-- Exact original typed enumerate, actual product/parameter/list/Code codecs,
unchanged eight blocks and prior/opened order. No boundedness/completeness claim. -/
def NativeOriginal : Prop := ∀ (n : Nat) (data : NumberedCodeEnumerationPrimrecSupportProof.Parameters n)
    (variableBound fuel : Nat),
  evaluate (enumeration n) (List.Vector.ofFn ![Encodable.encode (variableBound,fuel),Encodable.encode data]) =
    Encodable.encode (NumberedAuxiliaryEnumeration.enumerate data.1 data.2.1 data.2.2.1 data.2.2.2 variableBound fuel)
/-- Universal internal nonfailure of this exact G, even on malformed raw node,
parameter or answer lists. Some[] is1; no valid/Some/positive-fuel premise. -/
def InternalNonfailure : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (n : Nat) (node answers param out : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 (OriginalEnumerationRecursionInterface.G n) out node answers param)) →
  Nonempty (Derivation body Delta (eqn out z).not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion.Targets
