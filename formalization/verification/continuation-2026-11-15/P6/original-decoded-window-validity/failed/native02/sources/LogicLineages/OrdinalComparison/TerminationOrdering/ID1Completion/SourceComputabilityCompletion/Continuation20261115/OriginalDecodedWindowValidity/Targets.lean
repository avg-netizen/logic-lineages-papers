module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Exact original Encodable instance, on all vectors/raw codes, not only images. -/
def NativeSymbols : Prop := ∀ (n : Nat) (v : List.Vector Nat 1),
  evaluate (symbols n) v = (Encodable.decode (α := List (Fin n)) (v.get 0)).isSome.toNat
/-- Exact original product decoder, including every malformed symbol list.
No numbered-type or list-code substitute is assumed. -/
def NativeWindow : Prop := ∀ (n : Nat) (v : List.Vector Nat 1),
  evaluate (window n) v = (Encodable.decode (α := ExchangeNumericSuppliers.Window n) (v.get 0)).isSome.toNat
/-- Internal quantification ranges over actual original list membership. -/
def memberMatrix {alpha : Type} (n : Nat) (raw : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  (graph2 contains (numeral 1) (raw.relabel Sum.inl) (.var (.inr 0))).imp
    (InternalLessThan.strictLess (.var (.inr 0)) (numeral n))
def boundedMembers {alpha : Type} (n : Nat) (raw : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (memberMatrix n raw)
/-- Genuine constructive all-raw characterization; no native reflection,
external list image or assumed decoded validity. -/
def InternalSymbols : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw : OTerm alpha),
  (Nonempty (Derivation body Delta (graph1 (symbols n) (numeral 1) raw)) ↔
   Nonempty (Derivation body Delta (boundedMembers n raw)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.Targets
