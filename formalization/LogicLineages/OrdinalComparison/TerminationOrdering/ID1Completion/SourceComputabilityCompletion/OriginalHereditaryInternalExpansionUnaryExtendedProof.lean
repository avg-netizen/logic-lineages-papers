module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionUnaryExtendedProof
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

/-- Bridge the literal firstJob output to the checked weight theorem.
All measured quantities are queried internally, not supplied by callers. -/
theorem extendedFromSelectors (parent child parentRaw childRaw input first parameter window gamma childParameter childGamma domain W V : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget childRaw child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hchildParam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter window childGamma)))
 (hcons : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode childGamma domain gamma)))
 (hjob : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob childRaw input parameter)))
 (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (suc z) input)))
 (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first input)))
 (hf2 : Nonempty (Derivation body Delta (graph2 (firstOf (.projection 0)) first input parameter)))
 (hfp : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstParameter childParameter input parameter)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child))) :
 Nonempty (Derivation body Delta (ltF V W)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
 have hchildPair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childRaw first childParameter)) :=
   binaryRecover InternalPairing.pairing (firstOf (.projection 0)) OriginalHereditaryExpansion.firstParameter
     childRaw first childParameter xs hjob hf2 hfp
 have hpfields := fieldsOfForget parent parentRaw input parameter window gamma hp hr hparam
 have hcfields := fieldsOfForget child childRaw first childParameter window childGamma hc hchildPair hchildParam
 apply measuresCases first first gamma _
 intro beta rho Theta firstCount secondCount count hrho hfn hsn hlen
 simp only [orderRename]
 have hp' := renameInto hpfields rho Theta hrho
 have hc' := renameInto hcfields rho Theta hrho
 simp only [fields,conjunctionRename,graph1Rename] at hp' hc'
 have ha' := renameInto ha rho Theta hrho
 have hf' := renameInto hf rho Theta hrho
 have hw' := renameInto hw rho Theta hrho
 have hv' := renameInto hv rho Theta hrho
 have hcons' := renameInto hcons rho Theta hrho
 rw [graph2Rename] at hcons'
 simp only [graph1Rename,sucRelabel,zRelabel] at ha' hf' hw' hv'
 exact OriginalHereditaryInternalWeightChildProof.unaryExtended body beta Theta
   (parent.relabel rho) (child.relabel rho) (input.relabel rho) (first.relabel rho)
   (gamma.relabel rho) (childGamma.relabel rho) (domain.relabel rho) count firstCount (W.relabel rho) (V.relabel rho)
   hp' hc' ha' hf' hfn hlen hcons' hw' hv'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionUnaryExtendedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionUnaryExtendedProof
