module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionDecorationProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The copied raw payload survives arbitrary annotation computations. -/
theorem forgetPair {n : Nat} (annotation raw : Program n) (out rawValue : OTerm alpha)
 (xs : Fin n → OTerm alpha)
 (ho : Nonempty (Derivation body Delta
   (programGraph (pairOf (leftOf annotation) (pairOf (rightOf annotation) raw)) out xs)))
 (hr : Nonempty (Derivation body Delta (programGraph raw rawValue xs))) :
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget rawValue out)) := by
 apply programCompositionCases InternalPairing.pairing
   ![leftOf annotation,pairOf (rightOf annotation) raw] out xs _ ho
 intro beta rho ys Theta hrho hpair hs
 simp only [graph1Rename]
 have hr' := renameInto hr rho Theta hrho
 simp only [programRename] at hr'
 have hright := pairOfRight (rightOf annotation) raw (ys 1) (rawValue.relabel rho)
   (fun i => (xs i).relabel rho) (hs 1) hr'
 have houter : Nonempty (Derivation body Theta
   (graph2 InternalPairing.pairing (out.relabel rho) (ys 0) (ys 1))) := by
   simpa only [graph2,twoTuple] using hpair
 let xx : Fin 1 → OTerm beta := Fin.cons (out.relabel rho) Fin.elim0
 have hinner : Nonempty (Derivation body Theta
   (programGraph (rightOf (.projection 0)) (ys 1) xx)) :=
   unaryValue InternalUnpair.right (.projection 0) (ys 1) (out.relabel rho) xx
     (pairRight (out.relabel rho) (ys 0) (ys 1) houter) (projectionValue 0 xx)
 exact unaryValue InternalUnpair.right (rightOf (.projection 0)) (rawValue.relabel rho) (ys 1) xx
   hright hinner

/-- Literal decorate graph, with no predicate on role, type, or annotation. -/
theorem decorateForget (index role typ parentRaw rawChild child : OTerm alpha)
 (h : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.decorate
   child index role typ parentRaw rawChild))) :
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget rawChild child)) := by
 let xs : Fin 5 → OTerm alpha := Fin.cons index (Fin.cons role (Fin.cons typ (Fin.cons parentRaw (Fin.cons rawChild Fin.elim0))))
 let a : Program 5 := .composition OriginalHereditaryAnnotatedExpansion.annotation
   ![.projection 0,.projection 1,.projection 2,.projection 3]
 exact forgetPair a (.projection 4) child rawChild xs h (projectionValue 4 xs)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionDecorationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionDecorationProof
