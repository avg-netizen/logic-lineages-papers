module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeRowMemo.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeRowMemo.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Exact original Cartesian dependency order for every binary constructor pair. -/
def OriginalBinaryDependencies : Prop := ∀ (n : Nat)
    (source target x0 x1 y0 y1 : NumberedAuxiliaryCoding.Code (Fin n)),
  NumberedSyntaxBoundsPrimrecSupportProof.children source = [x0,x1] →
  NumberedSyntaxBoundsPrimrecSupportProof.children target = [y0,y1] →
  NumberedExchangeCodeFieldsProof.dependencies (source,target) =
    [(x0,y0),(x0,y1),(x1,y0),(x1,y1)]
/-- Actual source-rank strict decrease AND target-bound preservation; does not
assert a different paired-rank algorithm or reflect this native fact internally. -/
def OriginalDependencyBounds : Prop := ∀ (n : Nat)
    (source target x y : NumberedAuxiliaryCoding.Code (Fin n)),
  (x,y) ∈ NumberedExchangeCodeFieldsProof.dependencies (source,target) →
  NumberedLeastCodeRepresentative.codeNumber x < NumberedLeastCodeRepresentative.codeNumber source ∧
  NumberedLeastCodeRepresentative.codeNumber y < NumberedLeastCodeRepresentative.codeNumber target
/-- Symbolic actual row-table tail, independent of any native supplier law. -/
def InternalTableTail : Prop := ∀ (B : Program 2) (R : Program 4)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (index window bound old next : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 (table B R) old index window bound)) →
  Nonempty (Derivation body Delta (graph3 (table B R) next (suc index) window bound)) →
  Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode old next))
/-- Genuine internal arbitrary-gap coherence, with unchanged window/bound. -/
def InternalTableDrop : Prop := ∀ (B : Program 2) (R : Program 4)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (index gap window bound small large : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 (table B R) small index window bound)) →
  Nonempty (Derivation body Delta (graph3 (table B R) large (OrdinaryArithmetic.addTerm index gap) window bound)) →
  Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.drop small gap large))
/-- Exact symbolic original source-row lookup. Target-column lookup and actual
row-constructor implementation remain separate obligations, not premises hidden
inside a supplier calibration. -/
def InternalRowLookup : Prop := ∀ (B : Program 2) (R : Program 4)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (index gap window bound value large : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 (row B R) value index window bound)) →
  Nonempty (Derivation body Delta (graph3 (table B R) large (OrdinaryArithmetic.addTerm index gap) window bound)) →
  Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value gap large))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeRowMemo.Targets
