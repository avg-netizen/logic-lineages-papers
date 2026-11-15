module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.MapDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.MapProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.MapStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable (E : Program 2)
attribute [local irreducible] programGraph

theorem stepValue (key rest param value out : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 E value key param)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out value rest))) :
    Nonempty (Derivation body Delta (graph3 (MapDefinitions.step E) out key rest param)) := by
  let xs : Fin 3 → OTerm alpha := ![key,rest,param]
  have he := binaryValue E (.projection 0) (.projection 2)
    value key param xs hv (projectionValue 0 xs) (projectionValue 2 xs)
  exact binaryValue InternalListCodec.consCode
    (.composition E ![.projection 0,.projection 2]) (.projection 1)
    out value rest xs hc he (projectionValue 1 xs)

theorem nilValue (param : OTerm alpha) :
    Nonempty (Derivation body Delta (graph2 (MapDefinitions.orderedMap E) z z param)) :=
  InternalRawListRecursionProof.nilValue (InternalAcceptance.constantZero 1) (MapDefinitions.step E)
    z (Fin.cons param Fin.elim0)
    (InternalAcceptanceConjunctionProof.constantZeroValue (Fin.cons param Fin.elim0))

theorem consValue (keys key tail param value rest out : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode keys key tail)))
    (hv : Nonempty (Derivation body Delta (graph2 E value key param)))
    (hr : Nonempty (Derivation body Delta (graph2 (MapDefinitions.orderedMap E) rest tail param)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out value rest))) :
    Nonempty (Derivation body Delta (graph2 (MapDefinitions.orderedMap E) out keys param)) :=
  InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 1) (MapDefinitions.step E)
    keys key tail rest out (Fin.cons param Fin.elim0) hk hr (stepValue E key rest param value out hv hc)

theorem presentAt (key rest param old value out code : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 E value key param)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) old key)))
    (hs : Nonempty (Derivation body Delta (graph3 (MapDefinitions.step E) out key rest param)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code value rest))) :
    Nonempty (Derivation body Delta (graph3 ExchangeMapGraph.mapStep out key rest old)) := by
  have he := valueUnique (MapDefinitions.step E) code out ![key,rest,param]
    (stepValue E key rest param value code hv hc) hs
  exact outputTransport ExchangeMapGraph.mapStep code out ![key,rest,old] he
    (ArgumentEntriesConsTable.MapProof.presentStep key old value rest code hl hc)

theorem present (key rest param old value out : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 E value key param)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) old key)))
    (hs : Nonempty (Derivation body Delta (graph3 (MapDefinitions.step E) out key rest param))) :
    Nonempty (Derivation body Delta (graph3 ExchangeMapGraph.mapStep out key rest old)) := by
  apply InternalAcceptanceSupportProof.programCases InternalListCodec.consCode (Fin.cons value (Fin.cons rest Fin.elim0)) _
  intro beta j Theta code hj hc
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename] at hc
  rw [InternalApplicationCertificateConstructorsSyntaxProof.graph3Rename]
  have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  rw [InternalApplicationCertificateConstructorsSyntaxProof.graph2Rename] at hvj
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  simp only [InternalApplicationCertificateConstructorsSyntaxProof.graph2Rename,InternalTagArithmeticSyntaxProof.sucRelabel] at hlj
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  rw [InternalApplicationCertificateConstructorsSyntaxProof.graph3Rename] at hsj
  exact presentAt E (key.relabel j) (rest.relabel j) (param.relabel j) (old.relabel j) (value.relabel j) (out.relabel j) code hvj hlj hsj hc

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.MapStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.MapStepProof
