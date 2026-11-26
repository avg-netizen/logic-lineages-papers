module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceHeadsFieldsBridge.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceHeadsFieldsBridge.CompositionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem rawMember (n : Nat) (arity : Fin n → Nat) (rawHead symbols types rawList : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 (OriginalSourceHeads.sourceHeads n arity) rawList symbols types)))
    (hm : Nonempty (Derivation body Delta (graph3 (OriginalSourceHeads.member n arity) (numeral 1) rawHead symbols types))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) rawList rawHead)) := by
  let xs : Fin 3 → OTerm alpha := ![rawHead,symbols,types]
  have hsource := binaryValue (OriginalSourceHeads.sourceHeads n arity) (.projection 1) (.projection 2)
    rawList symbols types xs hs (projectionValue 1 xs) (projectionValue 2 xs)
  exact binaryRecover contains (.composition (OriginalSourceHeads.sourceHeads n arity) ![.projection 1,.projection 2])
    (.projection 0) (numeral 1) rawList rawHead xs hm hsource (projectionValue 0 xs)

theorem mapped (n : Nat) (arity : Fin n → Nat) (seed param symbols types rawList heads : OTerm alpha)
    (hsy : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.symbols symbols seed param)))
    (hty : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.types types seed param)))
    (hs : Nonempty (Derivation body Delta (graph2 (OriginalSourceHeads.sourceHeads n arity) rawList symbols types)))
    (hh : Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.heads n arity) heads seed param))) :
    Nonempty (Derivation body Delta (graph1 (InternalListMap.map OriginalHeadEncodingBridge.encodeHead) heads rawList)) := by
  let xs : Fin 2 → OTerm alpha := ![seed,param]
  have hsource := binaryValue (OriginalSourceHeads.sourceHeads n arity) OriginalClassCodes.symbols OriginalClassCodes.types
    rawList symbols types xs hs hsy hty
  exact unaryRecover (InternalListMap.map OriginalHeadEncodingBridge.encodeHead)
    (.composition (OriginalSourceHeads.sourceHeads n arity) ![OriginalClassCodes.symbols,OriginalClassCodes.types])
    heads rawList xs hh hsource

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceHeadsFieldsBridge.CompositionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceHeadsFieldsBridge.CompositionProof
