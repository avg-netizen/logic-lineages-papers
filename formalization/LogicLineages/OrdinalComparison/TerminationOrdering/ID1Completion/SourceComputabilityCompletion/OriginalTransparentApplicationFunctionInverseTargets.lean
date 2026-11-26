module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathInternalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceApplicationFieldsTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInverseTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Inversion of the actual original structural guard. Target constructor,
unchanged argument, arrow type and certificate lift are conclusions, not oracles. -/
def ActualInverse : Prop := ∀ (S : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter arrow d e fp ap fn arg targetFn childCert : OTerm alpha),
 Nonempty (Derivation body Delta (InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg s)) →
 Nonempty (Derivation body Delta (graph4 (OriginalTransparentApplicationFunctionDefinitions.hopGuard S) (numeral 1) s t cert parameter)) →
 Nonempty (Derivation body Delta (graph4 OriginalTransparentApplicationFunctionDefinitions.targetFunction targetFn s t cert parameter)) →
 Nonempty (Derivation body Delta (graph4 OriginalTransparentApplicationFunctionDefinitions.childCertificate childCert s t cert parameter)) →
 Nonempty (Derivation body Delta (OriginalTransparentMixedPathInternalDefinitions.ApplicationHop S s t cert parameter fn targetFn childCert arg d e arrow))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInverseTargets
