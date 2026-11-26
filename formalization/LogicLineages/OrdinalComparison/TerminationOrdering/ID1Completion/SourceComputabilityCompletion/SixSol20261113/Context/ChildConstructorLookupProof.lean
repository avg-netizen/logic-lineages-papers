module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildRawLookupProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildConstructorLookupProof
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

theorem applicationLookup (raw domain first second parameter jobs raw0 raw1 : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.applicationConstructor raw domain first second)))
    (h0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw0 first parameter)))
    (h1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw1 second parameter)))
    (he : Nonempty (Derivation body Delta (graph2 expansion jobs raw parameter))) :
    Nonempty (Derivation body Delta ((graph2 InternalRawListRecursion.lookup raw0 z jobs) ⊓
      (graph2 InternalRawListRecursion.lookup raw1 (numeral 1) jobs))) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  have htag := applicationTag (.projection 0) raw domain first second xs (projectionValue 0 xs) hc
  have ha := applicationArity (.projection 0) raw domain first second xs (projectionValue 0 xs) hc
  have hf := applicationFirst (.projection 0) raw domain first second xs (projectionValue 0 xs) hc
  have hs := applicationSecond (.projection 0) raw domain first second xs (projectionValue 0 xs) hc
  have hparameter := OriginalHereditaryInternalExpansionChildrenProof.firstParameterSameValue
    2 (by decide) xs parameter htag (projectionValue 1 xs)
  have hfirst := binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.firstOf (.projection 0)) firstParameter
    raw0 first parameter xs h0 hf hparameter
  have hsecond := binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.secondOf (.projection 0)) (.projection 1)
    raw1 second parameter xs h1 hs (projectionValue 1 xs)
  exact ChildRawLookupProof.actual raw parameter jobs raw0 raw1 ha hfirst hsecond he

theorem consLookup (raw domain first second parameter jobs raw0 raw1 : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw domain first second)))
    (h0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw0 first parameter)))
    (h1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw1 second parameter)))
    (he : Nonempty (Derivation body Delta (graph2 expansion jobs raw parameter))) :
    Nonempty (Derivation body Delta ((graph2 InternalRawListRecursion.lookup raw0 z jobs) ⊓
      (graph2 InternalRawListRecursion.lookup raw1 (numeral 1) jobs))) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  have htag := consTag (.projection 0) raw domain first second xs (projectionValue 0 xs) hc
  have ha := consArity (.projection 0) raw domain first second xs (projectionValue 0 xs) hc
  have hf := consFirst (.projection 0) raw domain first second xs (projectionValue 0 xs) hc
  have hs := consSecond (.projection 0) raw domain first second xs (projectionValue 0 xs) hc
  have hparameter := OriginalHereditaryInternalExpansionChildrenProof.firstParameterSameValue
    7 (by decide) xs parameter htag (projectionValue 1 xs)
  have hfirst := binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.firstOf (.projection 0)) firstParameter
    raw0 first parameter xs h0 hf hparameter
  have hsecond := binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.secondOf (.projection 0)) (.projection 1)
    raw1 second parameter xs h1 hs (projectionValue 1 xs)
  exact ChildRawLookupProof.actual raw parameter jobs raw0 raw1 ha hfirst hsecond he
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildConstructorLookupProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildConstructorLookupProof
