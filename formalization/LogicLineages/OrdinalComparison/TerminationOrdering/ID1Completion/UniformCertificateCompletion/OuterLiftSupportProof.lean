module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterCarrierSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterLiftSupportProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalComputabilityApplication InternalAccessibilityRules InternalComputabilityDownward
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- Recover the supplied ORIGINAL mapper output at the actual symbolic
context/Gamma parameter and RAW argument. No new certificate field appears. -/
theorem mappedRecover (data : Data) (window : Program 1) (oldVertex : Program 5)
    (context : Nat) (sigma tau : Ty) (a witness lifted gammaCode argument parameter : OTerm α)
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode a)))
    (ha : Nonempty (Derivation body Delta (graph1 InternalUnpair.right argument a)))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter (numeral context) gammaCode)))
    (hl : Nonempty (Derivation body Delta
      (programGraph (Outer.lift data window oldVertex) lifted
        (liftArguments context sigma tau a witness)))) :
    Nonempty (Derivation body Delta
      (InternalApplicationPathMap.mapGraph (Path.vertex data window oldVertex)
        lifted witness parameter (numeral (typeNumber sigma)) (numeral (typeNumber tau)) argument)) := by
  let xs := liftArguments context sigma tau a witness
  have hparameter := OuterCarrierSupportProof.parameterValue (.projection (0 : Fin 5)) (.projection 3)
    (numeral context) a gammaCode parameter xs (projectionValue 0 xs) (projectionValue 3 xs) hg hp
  have hargument := unaryValue InternalUnpair.right (.projection (3 : Fin 5)) argument a xs
    ha (projectionValue 3 xs)
  apply compositionRecover (InternalApplicationPathMap.pathMap (Path.vertex data window oldVertex))
    (Fin.cons (.projection 4) (Fin.cons (Outer.parameter (.projection 0) (.projection 3))
      (Fin.cons (.projection 1) (Fin.cons (.projection 2)
        (Fin.cons (rightOf (.projection 3)) Fin.elim0))))) lifted xs
    (Fin.cons witness (Fin.cons parameter (Fin.cons (numeral (typeNumber sigma))
      (Fin.cons (numeral (typeNumber tau)) (Fin.cons argument Fin.elim0))))) hl
  intro i
  exact Fin.cases (projectionValue 4 xs) (Fin.cases hparameter (Fin.cases (projectionValue 1 xs)
    (Fin.cases (projectionValue 2 xs) (Fin.cases hargument (fun j => Fin.elim0 j))))) i

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterLiftSupportProof
