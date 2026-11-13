module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildRawLookupProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NumberedConstructorProof
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

theorem lookup (raw label head encodedType base extraTypes extras parameter jobs raw0 raw1 : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw (Fin.cons label (Fin.cons head (Fin.cons encodedType (Fin.cons base (Fin.cons extraTypes (Fin.cons extras Fin.elim0)))))))))
    (h0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw0 base parameter)))
    (h1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw1 extras parameter)))
    (he : Nonempty (Derivation body Delta (graph2 expansion jobs raw parameter))) :
    Nonempty (Derivation body Delta ((graph2 InternalRawListRecursion.lookup raw0 z jobs) ⊓
      (graph2 InternalRawListRecursion.lookup raw1 (numeral 1) jobs))) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  have htag := numberedTag (.projection 0) raw label head encodedType base extraTypes extras xs (projectionValue 0 xs) hc
  have ha := numberedArity (.projection 0) raw label head encodedType base extraTypes extras xs (projectionValue 0 xs) hc
  have hf := numberedFirst (.projection 0) raw label head encodedType base extraTypes extras xs (projectionValue 0 xs) hc
  have hs := numberedSecond (.projection 0) raw label head encodedType base extraTypes extras xs (projectionValue 0 xs) hc
  have hparameter := OriginalHereditaryInternalExpansionChildrenProof.firstParameterSameValue
    5 (by decide) xs parameter htag (projectionValue 1 xs)
  have hfirst := binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.firstOf (.projection 0)) firstParameter
    raw0 base parameter xs h0 hf hparameter
  have hsecond := binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.secondOf (.projection 0)) (.projection 1)
    raw1 extras parameter xs h1 hs (projectionValue 1 xs)
  exact ChildRawLookupProof.actual raw parameter jobs raw0 raw1 ha hfirst hsecond he

theorem pair (raw label head encodedType base extraTypes extras afterBase numberedFields afterHead afterLabel payload : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw (Fin.cons label (Fin.cons head (Fin.cons encodedType (Fin.cons base (Fin.cons extraTypes (Fin.cons extras Fin.elim0)))))))))
    (h0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing afterBase extraTypes extras)))
    (h1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing numberedFields base afterBase)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing afterHead encodedType numberedFields)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing afterLabel head afterHead)))
    (h4 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload label afterLabel)))
    : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 5) payload)) := by
  let xs : Fin 6 → OTerm alpha := ![label,head,encodedType,base,extraTypes,extras]
  let p0 : Program 6 := pairOf (.projection 4) (.projection 5)
  let p1 : Program 6 := pairOf (.projection 3) p0
  let p2 : Program 6 := pairOf (.projection 2) p1
  let p3 : Program 6 := pairOf (.projection 1) p2
  let p4 : Program 6 := pairOf (.projection 0) p3
  have b0 := binaryValue InternalPairing.pairing (.projection 4) (.projection 5) afterBase extraTypes extras xs h0 (projectionValue 4 xs) (projectionValue 5 xs)
  have b1 := binaryValue InternalPairing.pairing (.projection 3) p0 numberedFields base afterBase xs h1 (projectionValue 3 xs) b0
  have b2 := binaryValue InternalPairing.pairing (.projection 2) p1 afterHead encodedType numberedFields xs h2 (projectionValue 2 xs) b1
  have b3 := binaryValue InternalPairing.pairing (.projection 1) p2 afterLabel head afterHead xs h3 (projectionValue 1 xs) b2
  have b4 := binaryValue InternalPairing.pairing (.projection 0) p3 payload label afterLabel xs h4 (projectionValue 0 xs) b3
  exact binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 6 5) p4 raw (numeral 5) payload xs hc (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 5 xs) b4
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NumberedConstructorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NumberedConstructorProof
