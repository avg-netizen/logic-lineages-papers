module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc z)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Exact original List Ty / List(List Ty) Encodable instances, on every raw
input. Total type-list decoding and both nested codec conversions must be proved,
not assumed. Source.Ty has no finite-symbol parameter. -/
def NativeEnumeration : Prop := ∀ (v : List.Vector Nat 2),
  evaluate enumeration v = Encodable.encode
    (NumberedAuxiliaryEnumeration.typeLists
      ((Encodable.decode (α := List Source.Ty) (v.get 1)).getD []) (v.get 0))
/-- The original base [[]] is the actual outer list with sole entry empty-list0. -/
def InternalZero : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (types : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 enumeration (numeral 1) z types))
/-- Literal successor reconstruction from actual prior enumeration and row-major
cross graph. No list-image, distinctness or valid-code assumption. The final
leading entry is empty-list0, not an omitted entry or a None marker. -/
def InternalSuccessor : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (count types previous rows out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 enumeration previous count types)) →
  Nonempty (Derivation body Delta (graph2 cross rows types previous)) →
  (Nonempty (Derivation body Delta (graph2 enumeration out (suc count) types)) ↔
   Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out z rows)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.Targets
