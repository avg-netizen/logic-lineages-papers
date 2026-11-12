module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionUnarySameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionChildrenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionOrdinaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalOriginalOrderSyntaxProof
open OriginalHereditaryInternalExpansionUnarySameProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem ordinaryFirst (parent child parentRaw childRaw input head base parameter window gamma W V : OTerm alpha)
 (hctor : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor input head base)))
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget childRaw child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hjob : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob childRaw input parameter)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child))) :
 Nonempty (Derivation body Delta (ltF V W)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
 let ys : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
 exact unaryFromSelectors parent child parentRaw childRaw input base parameter window gamma W V
   hp hc hr hparam hjob
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.ordinaryArity (.projection 0) input head base xs (projectionValue 0 xs) hctor)
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.ordinaryFirst (.projection 0) input head base xs (projectionValue 0 xs) hctor)
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.ordinaryFirst (.projection 0) input head base ys (projectionValue 0 ys) hctor)
   (OriginalHereditaryInternalExpansionChildrenProof.firstParameterSameValue 4 (by decide) ys parameter
     (OriginalRawSyntaxTransportInternalConstructorFieldsProof.ordinaryTag (.projection 0) input head base ys (projectionValue 0 ys) hctor)
     (projectionValue 1 ys))
   hw hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionOrdinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionOrdinaryProof
