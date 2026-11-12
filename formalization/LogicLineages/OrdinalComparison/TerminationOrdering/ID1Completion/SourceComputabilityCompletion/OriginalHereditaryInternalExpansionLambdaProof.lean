module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLambdaParameterProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionChildrenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalOriginalOrderSyntaxProof
open OriginalHereditaryInternalExpansionLambdaParameterProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalGraphCompositionFunctionalityProof
open OriginalHereditaryInternalExpansionLambdaParameterProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem lambdaFirst (parent child parentRaw childRaw input domain term parameter window gamma W V : OTerm alpha)
 (hctor : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor input domain term)))
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget childRaw child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hjob : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob childRaw input parameter)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child))) :
 Nonempty (Derivation body Delta (ltF V W)) := by
 apply extensionCases domain gamma window _
 intro beta rho Theta extended childParameter hrho hcons hchildParam
 simp only [orderRename]
 have hctor' := renameInto hctor rho Theta hrho
 have hp' := renameInto hp rho Theta hrho
 have hc' := renameInto hc rho Theta hrho
 have hr' := renameInto hr rho Theta hrho
 have hparam' := renameInto hparam rho Theta hrho
 have hjob' := renameInto hjob rho Theta hrho
 have hw' := renameInto hw rho Theta hrho
 have hv' := renameInto hv rho Theta hrho
 simp only [graph1Rename,graph2Rename] at hctor' hp' hc' hr' hparam' hjob' hw' hv'
 let xs : Fin 1 → OTerm beta := Fin.cons (input.relabel rho) Fin.elim0
 let ys : Fin 2 → OTerm beta := Fin.cons (input.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)
 exact OriginalHereditaryInternalExpansionUnaryExtendedProof.extendedFromSelectors
   (parent.relabel rho) (child.relabel rho) (parentRaw.relabel rho) (childRaw.relabel rho)
   (input.relabel rho) (term.relabel rho) (parameter.relabel rho) (window.relabel rho)
   (gamma.relabel rho) childParameter extended (domain.relabel rho) (W.relabel rho) (V.relabel rho)
   hp' hc' hr' hparam' hchildParam hcons hjob'
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.lambdaArity (.projection 0)
     (input.relabel rho) (domain.relabel rho) (term.relabel rho) xs (projectionValue 0 xs) hctor')
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.lambdaFirst (.projection 0)
     (input.relabel rho) (domain.relabel rho) (term.relabel rho) xs (projectionValue 0 xs) hctor')
   (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.lambdaFirst (.projection 0)
     (input.relabel rho) (domain.relabel rho) (term.relabel rho) ys (projectionValue 0 ys) hctor')
   (parameterValue (input.relabel rho) (domain.relabel rho) (term.relabel rho)
     (parameter.relabel rho) (window.relabel rho) (gamma.relabel rho) extended childParameter
     hctor' hparam' hcons hchildParam) hw' hv'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLambdaProof
