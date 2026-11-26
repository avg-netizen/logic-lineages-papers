module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionFirstSameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionChildrenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionFirstConstructorsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalOriginalOrderSyntaxProof
open OriginalHereditaryInternalExpansionFirstSameProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem applicationFirst (parent child parentRaw childRaw input domain fn arg parameter window gamma W V : OTerm alpha)
 (hctor : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.applicationConstructor input domain fn arg)))
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
 exact firstFromSelectors parent child parentRaw childRaw input fn arg parameter window gamma W V
   hp hc hr hparam hjob
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.applicationArity (.projection 0) input domain fn arg xs (projectionValue 0 xs) hctor)
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.applicationFirst (.projection 0) input domain fn arg xs (projectionValue 0 xs) hctor)
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.applicationSecond (.projection 0) input domain fn arg xs (projectionValue 0 xs) hctor)
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.applicationFirst (.projection 0) input domain fn arg ys (projectionValue 0 ys) hctor)
   (OriginalHereditaryInternalExpansionChildrenProof.firstParameterSameValue 2 (by decide) ys parameter
     (OriginalRawSyntaxTransportInternalConstructorFieldsProof.applicationTag (.projection 0) input domain fn arg ys (projectionValue 0 ys) hctor)
     (projectionValue 1 ys))
   hw hv

theorem consFirst (parent child parentRaw childRaw input typ head tail parameter window gamma W V : OTerm alpha)
 (hctor : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor input typ head tail)))
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
 exact firstFromSelectors parent child parentRaw childRaw input head tail parameter window gamma W V
   hp hc hr hparam hjob
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.consArity (.projection 0) input typ head tail xs (projectionValue 0 xs) hctor)
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.consFirst (.projection 0) input typ head tail xs (projectionValue 0 xs) hctor)
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.consSecond (.projection 0) input typ head tail xs (projectionValue 0 xs) hctor)
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.consFirst (.projection 0) input typ head tail ys (projectionValue 0 ys) hctor)
   (OriginalHereditaryInternalExpansionChildrenProof.firstParameterSameValue 7 (by decide) ys parameter
     (OriginalRawSyntaxTransportInternalConstructorFieldsProof.consTag (.projection 0) input typ head tail ys (projectionValue 0 ys) hctor)
     (projectionValue 1 ys))
   hw hv

theorem numberedFirst (parent child parentRaw childRaw input label head typ base types extras parameter window gamma W V : OTerm alpha)
 (hctor : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor input (Fin.cons label (Fin.cons head (Fin.cons typ (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0)))))))))
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
 exact firstFromSelectors parent child parentRaw childRaw input base extras parameter window gamma W V
   hp hc hr hparam hjob
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.numberedArity (.projection 0) input label head typ base types extras xs (projectionValue 0 xs) hctor)
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.numberedFirst (.projection 0) input label head typ base types extras xs (projectionValue 0 xs) hctor)
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.numberedSecond (.projection 0) input label head typ base types extras xs (projectionValue 0 xs) hctor)
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.numberedFirst (.projection 0) input label head typ base types extras ys (projectionValue 0 ys) hctor)
   (OriginalHereditaryInternalExpansionChildrenProof.firstParameterSameValue 5 (by decide) ys parameter
     (OriginalRawSyntaxTransportInternalConstructorFieldsProof.numberedTag (.projection 0) input label head typ base types extras ys (projectionValue 0 ys) hctor)
     (projectionValue 1 ys))
   hw hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionFirstConstructorsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionFirstConstructorsProof
