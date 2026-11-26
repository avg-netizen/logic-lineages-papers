module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionDecorationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalDecorationCoordinatesTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalDecorationCoordinatesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalRecursionGraphStepSyntaxProof
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeel (graph5)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem pairRecover {n : Nat} (p q : Program n) (out x y : OTerm alpha) (xs : Fin n → OTerm alpha)
 (ho : Nonempty (Derivation body Delta (programGraph (pairOf p q) out xs)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out x y))) :
 Nonempty (Derivation body Delta ((programGraph p x xs) ⊓ (programGraph q y xs))) := by
 apply programCompositionCases InternalPairing.pairing ![p,q] out xs _ ho
 intro beta rho ys Theta hrho hpair hs
 simp only [conjunctionRename,programRename]
 have hp' := renameInto hp rho Theta hrho
 simp only [graph2Rename] at hp'
 have hpair' : Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (out.relabel rho) (ys 0) (ys 1))) := by
   simpa only [graph2,twoTuple] using hpair
 have hx := valueUnique InternalUnpair.left (ys 0) (x.relabel rho) (Fin.cons (out.relabel rho) Fin.elim0)
   (pairLeft _ _ _ hpair') (pairLeft _ _ _ hp')
 have hy := valueUnique InternalUnpair.right (ys 1) (y.relabel rho) (Fin.cons (out.relabel rho) Fin.elim0)
   (pairRight _ _ _ hpair') (pairRight _ _ _ hp')
 exact andIntro (outputTransport p _ _ _ hx (hs 0)) (outputTransport q _ _ _ hy (hs 1))

theorem annotationRecover {n : Nat} (a : Program n) (annotation childRole childType : OTerm alpha)
 (xs : Fin n → OTerm alpha)
 (hl0 : Nonempty (Derivation body Delta (programGraph (leftOf a) childRole xs)))
 (hr0 : Nonempty (Derivation body Delta (programGraph (rightOf a) childType xs)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing annotation childRole childType))) :
 Nonempty (Derivation body Delta (programGraph a annotation xs)) := by
 apply programCases a xs _
 intro beta rho Theta value hrho hv
 simp only [programRename]
 have hl := renameInto hl0 rho Theta hrho
 have hr := renameInto hr0 rho Theta hrho
 have ha' := renameInto ha rho Theta hrho
 simp only [programRename] at hl hr
 simp only [graph2Rename] at ha'
 have hleft := unaryRecover InternalUnpair.left a (childRole.relabel rho) value (fun i => (xs i).relabel rho) hl hv
 have hright := unaryRecover InternalUnpair.right a (childType.relabel rho) value (fun i => (xs i).relabel rho) hr hv
 have he := valueUnique InternalPairing.pairing value (annotation.relabel rho)
   (Fin.cons (childRole.relabel rho) (Fin.cons (childType.relabel rho) Fin.elim0))
   (reconstructPair value _ _ hleft hright) ha'
 exact outputTransport a value (annotation.relabel rho) (fun i => (xs i).relabel rho) he hv

theorem actualCoordinates : OriginalInternalDecorationCoordinatesTargets.ActualCoordinates := by
 intro body alpha Delta index role typ raw rawChild child childRole childType typed annotation hd hc ht ha
 let xs : Fin 5 → OTerm alpha := Fin.cons index (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons rawChild Fin.elim0))))
 let a : Program 5 := .composition OriginalHereditaryAnnotatedExpansion.annotation ![.projection 0,.projection 1,.projection 2,.projection 3]
 have outer := pairRecover (leftOf a) (pairOf (rightOf a) (.projection 4)) child childRole typed xs hd hc
 have inner := pairRecover (rightOf a) (.projection 4) typed childType rawChild xs (andRight outer) ht
 have hav := annotationRecover a annotation childRole childType xs (andLeft outer) (andLeft inner) ha
 exact compositionRecover OriginalHereditaryAnnotatedExpansion.annotation
   ![.projection 0,.projection 1,.projection 2,.projection 3]
   annotation xs
   (Fin.cons index (Fin.cons role (Fin.cons typ (Fin.cons raw Fin.elim0))))
   hav (by
     intro i
     refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)))) i
     · exact projectionValue 0 xs
     · exact projectionValue 1 xs
     · exact projectionValue 2 xs
     · exact projectionValue 3 xs)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalDecorationCoordinatesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalDecorationCoordinatesProof
