module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionSecondProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open InternalOriginalOrderSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryInternalWeightDefinitions
open OriginalHereditaryInternalExpansionFieldsProof OriginalHereditaryInternalExpansionMeasureProof
open OriginalRawSyntaxTransport (firstOf secondOf arityOf)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Bridge the literal secondJob output to the checked weight theorem.
All measured quantities are queried internally, not supplied by callers. -/
theorem secondFromSelectors (parent child parentRaw childRaw input first second parameter window gamma W V : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget childRaw child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hjob : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob childRaw input parameter)))
 (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (suc (suc z)) input)))
 (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first input)))
 (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second input)))
 (hs2 : Nonempty (Derivation body Delta (graph2 (secondOf (.projection 0)) second input parameter)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child))) :
 Nonempty (Derivation body Delta (ltF V W)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
 have hchildPair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childRaw second parameter)) :=
   binaryRecover InternalPairing.pairing (secondOf (.projection 0)) (.projection 1)
     childRaw second parameter xs hjob hs2 (projectionValue 1 xs)
 have hpfields := fieldsOfForget parent parentRaw input parameter window gamma hp hr hparam
 have hcfields := fieldsOfForget child childRaw second parameter window gamma hc hchildPair hparam
 apply measuresCases first second gamma _
 intro beta rho Theta firstCount secondCount count hrho hfn hsn hlen
 simp only [orderRename]
 have hp' := renameInto hpfields rho Theta hrho
 have hc' := renameInto hcfields rho Theta hrho
 simp only [fields,conjunctionRename,graph1Rename] at hp' hc'
 have ha' := renameInto ha rho Theta hrho
 have hf' := renameInto hf rho Theta hrho
 have hs' := renameInto hs rho Theta hrho
 have hw' := renameInto hw rho Theta hrho
 have hv' := renameInto hv rho Theta hrho
 simp only [graph1Rename,sucRelabel,zRelabel] at ha' hf' hs' hw' hv'
 exact OriginalHereditaryInternalWeightChildProof.binarySecond body beta Theta
   (parent.relabel rho) (child.relabel rho) (input.relabel rho) (first.relabel rho) (second.relabel rho)
   (gamma.relabel rho) count firstCount secondCount (W.relabel rho) (V.relabel rho)
   hp' hc' ha' hf' hs' hfn hsn hlen hw' hv'

theorem applicationSecond (parent child parentRaw childRaw input domain fn arg parameter window gamma W V : OTerm alpha)
 (hctor : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.applicationConstructor input domain fn arg)))
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget childRaw child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hjob : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob childRaw input parameter)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child))) :
 Nonempty (Derivation body Delta (ltF V W)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
 let ys : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
 exact secondFromSelectors parent child parentRaw childRaw input fn arg parameter window gamma W V
   hp hc hr hparam hjob
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.applicationArity (.projection 0) input domain fn arg xs (projectionValue 0 xs) hctor)
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.applicationFirst (.projection 0) input domain fn arg xs (projectionValue 0 xs) hctor)
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.applicationSecond (.projection 0) input domain fn arg xs (projectionValue 0 xs) hctor)
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.applicationSecond (.projection 0) input domain fn arg ys (projectionValue 0 ys) hctor)
   hw hv

theorem consSecond (parent child parentRaw childRaw input typ head tail parameter window gamma W V : OTerm alpha)
 (hctor : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor input typ head tail)))
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget childRaw child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hjob : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob childRaw input parameter)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child))) :
 Nonempty (Derivation body Delta (ltF V W)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
 let ys : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
 exact secondFromSelectors parent child parentRaw childRaw input head tail parameter window gamma W V
   hp hc hr hparam hjob
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.consArity (.projection 0) input typ head tail xs (projectionValue 0 xs) hctor)
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.consFirst (.projection 0) input typ head tail xs (projectionValue 0 xs) hctor)
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.consSecond (.projection 0) input typ head tail xs (projectionValue 0 xs) hctor)
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.consSecond (.projection 0) input typ head tail ys (projectionValue 0 ys) hctor)
   hw hv

theorem numberedSecond (parent child parentRaw childRaw input label head typ base types extras parameter window gamma W V : OTerm alpha)
 (hctor : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor input (Fin.cons label (Fin.cons head (Fin.cons typ (Fin.cons base (Fin.cons types (Fin.cons extras Fin.elim0)))))))))
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget childRaw child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hjob : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob childRaw input parameter)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child))) :
 Nonempty (Derivation body Delta (ltF V W)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
 let ys : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
 exact secondFromSelectors parent child parentRaw childRaw input base extras parameter window gamma W V
   hp hc hr hparam hjob
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.numberedArity (.projection 0) input label head typ base types extras xs (projectionValue 0 xs) hctor)
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.numberedFirst (.projection 0) input label head typ base types extras xs (projectionValue 0 xs) hctor)
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.numberedSecond (.projection 0) input label head typ base types extras xs (projectionValue 0 xs) hctor)
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.numberedSecond (.projection 0) input label head typ base types extras ys (projectionValue 0 ys) hctor)
   hw hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionSecondProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionSecondProof
