module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryRawLookupProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildDecorationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryConstructorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryExpansion
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem zeroBelowOne : Nonempty (Derivation body Delta
    (InternalOriginalOrderSyntaxProof.ltF (z : OTerm alpha) (numeral 1))) := by
  apply InternalOriginalOrderProof.actualOriginalOrderIntroduction body alpha Delta z (numeral 1) z
  rw [InternalSourceInversionSupportProof.onEquality]
  exact ⟨InternalAdditionLawsProof.leftZero (numeral 1)⟩

theorem lambdaPair (raw domain child payload : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor raw domain child)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload domain child))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 1) payload)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons domain (Fin.cons child Fin.elim0)
  have hv := binaryValue InternalPairing.pairing (.projection 0) (.projection 1) payload domain child xs
    hp (projectionValue 0 xs) (projectionValue 1 xs)
  exact binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 1) (pairOf (.projection 0) (.projection 1))
    raw (numeral 1) payload xs hc (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 1 xs) hv

theorem ordinaryPair (raw domain child payload : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw domain child)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload domain child))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 4) payload)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons domain (Fin.cons child Fin.elim0)
  have hv := binaryValue InternalPairing.pairing (.projection 0) (.projection 1) payload domain child xs
    hp (projectionValue 0 xs) (projectionValue 1 xs)
  exact binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 4) (pairOf (.projection 0) (.projection 1))
    raw (numeral 4) payload xs hc (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 4 xs) hv

theorem ordinaryLookup (raw head base parameter jobs rawCell : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw head base)))
    (h0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawCell base parameter)))
    (he : Nonempty (Derivation body Delta (graph2 expansion jobs raw parameter))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rawCell z jobs)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  have htag := ordinaryTag (.projection 0) raw head base xs (projectionValue 0 xs) hc
  have ha := ordinaryArity (.projection 0) raw head base xs (projectionValue 0 xs) hc
  have hf := ordinaryFirst (.projection 0) raw head base xs (projectionValue 0 xs) hc
  have hparameter := OriginalHereditaryInternalExpansionChildrenProof.firstParameterSameValue
    4 (by decide) xs parameter htag (projectionValue 1 xs)
  have hfirst := binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.firstOf (.projection 0)) firstParameter
    rawCell base parameter xs h0 hf hparameter
  exact UnaryRawLookupProof.actual raw parameter jobs rawCell ha hfirst he

theorem lambdaLookup (raw domain child parameter childParameter jobs rawCell : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor raw domain child)))
    (h0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawCell child childParameter)))
    (hparameter : Nonempty (Derivation body Delta (graph2 firstParameter childParameter raw parameter)))
    (he : Nonempty (Derivation body Delta (graph2 expansion jobs raw parameter))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rawCell z jobs)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  have ha := lambdaArity (.projection 0) raw domain child xs (projectionValue 0 xs) hc
  have hf := lambdaFirst (.projection 0) raw domain child xs (projectionValue 0 xs) hc
  have hfirst := binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.firstOf (.projection 0)) firstParameter
    rawCell child childParameter xs h0 hf hparameter
  exact UnaryRawLookupProof.actual raw parameter jobs rawCell ha hfirst he
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryConstructorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryConstructorProof
