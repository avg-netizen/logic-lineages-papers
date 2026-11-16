module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteSignatureEquations.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSignatureStructure.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalConcreteHeadSignature
/-- Basic head tag0 returns ground and tag1 returns arrow(ground,ground),
whose original numeric codes are respectively0 and1. Both require payload0. -/
def BasicEquation : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (tag : Fin 2) (raw packed out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral tag.val) z)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed (numeral tag.val) z)) →
  (Nonempty (Derivation body Delta (graph1 (signature n arity) out raw)) ↔
   Nonempty (Derivation body Delta (eqn out (suc packed))))
/-- The case result is ground → tau → tau → tau, with actual pair witnesses
for every arrow, and empty arguments. No result-program success is supplied. -/
def CaseEquation : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw tau aa ab ac packed out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 2) tau)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing aa tau tau)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ab tau (suc aa))) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ac z (suc ab))) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed (suc ac) z)) →
  (Nonempty (Derivation body Delta (graph1 (signature n arity) out raw)) ↔
   Nonempty (Derivation body Delta (eqn out (suc packed))))
/-- Recursor result is ground → (ground → tau → tau) → tau → tau.
All nested type codes are actual arithmetic pair witnesses. -/
def RecursorEquation : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw tau aa ab ac ad packed out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 3) tau)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing aa tau tau)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ab z (suc aa))) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ac (suc ab) (suc aa))) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ad z (suc ac))) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed (suc ad) z)) →
  (Nonempty (Derivation body Delta (graph1 (signature n arity) out raw)) ↔
   Nonempty (Derivation body Delta (eqn out (suc packed))))
/-- One coherent endpoint completes all four remaining source head cases. -/
def InternalBuiltinSignatures : Prop := BasicEquation ∧ CaseEquation ∧ RecursorEquation
/-- Actual internal length and ground-type contents for the literal ranked
argument-list recursion. Lookup is zero even out of range, as in the ORIGINAL
lookup convention; length prevents this from mistaking an empty list for a
nonempty ground list. No native decoding or encoded-image restriction. -/
def InternalGroundListStructure : Prop := ∀ (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (count args : OTerm alpha),
  Nonempty (Derivation body Delta (graph1 groundList args count)) →
  Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count args)) ∧
  (∀ (index : OTerm alpha),
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup z index args)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSignatureStructure.Targets
