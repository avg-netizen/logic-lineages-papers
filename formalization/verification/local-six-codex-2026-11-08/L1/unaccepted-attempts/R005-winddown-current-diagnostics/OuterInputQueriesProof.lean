module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterInputQueriesDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterCarrierSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterInputQueriesProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

theorem parameterRecover (context : Nat) (xs : Fin 3 → OTerm α) (gammaCode parameter : OTerm α)
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode (xs 0))))
    (hp : Nonempty (Derivation body Delta
      (programGraph (OuterInputQueries.parameter context) parameter xs))) :
    Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter (numeral context) gammaCode)) :=
  OuterCarrierSupportProof.parameterRecover (Path.constant 3 context) (.projection 0)
    (numeral context) (xs 0) gammaCode parameter xs
    (PathSupportProof.constantValue 3 context xs) (projectionValue 0 xs) hg hp

theorem rawVertexRecover (data : Data) (window : Program 1) (oldVertex : Program 5)
    (context : Nat) (sigma tau : Ty) (function : Fin 3) (xs : Fin 3 → OTerm α)
    (parameter argument x value : OTerm α)
    (hp : Nonempty (Derivation body Delta
      (programGraph (OuterInputQueries.parameter context) parameter xs)))
    (ha : Nonempty (Derivation body Delta (graph1 InternalUnpair.right argument (xs 2))))
    (hx : Nonempty (Derivation body Delta (graph1 InternalUnpair.right x (xs function))))
    (hv : Nonempty (Derivation body Delta
      (programGraph (OuterInputQueries.rawVertex data window oldVertex context sigma tau function) value xs))) :
    Nonempty (Derivation body Delta
      (graph5 (Path.vertex data window oldVertex) value parameter
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) argument x)) := by
  apply compositionRecover (Path.vertex data window oldVertex)
    (Fin.cons (OuterInputQueries.parameter context) (Fin.cons (Path.constant 3 (typeNumber sigma))
      (Fin.cons (Path.constant 3 (typeNumber tau))
        (Fin.cons (rightOf (.projection 2)) (Fin.cons (rightOf (.projection function)) Fin.elim0)))))
    value xs (Fin.cons parameter (Fin.cons (numeral (typeNumber sigma))
      (Fin.cons (numeral (typeNumber tau)) (Fin.cons argument (Fin.cons x Fin.elim0))))) hv
  intro i
  exact Fin.cases hp (Fin.cases (PathSupportProof.constantValue 3 (typeNumber sigma) xs)
    (Fin.cases (PathSupportProof.constantValue 3 (typeNumber tau) xs)
      (Fin.cases (unaryValue InternalUnpair.right (.projection (2 : Fin 3)) argument (xs 2) xs
        ha (projectionValue 2 xs))
        (Fin.cases (unaryValue InternalUnpair.right (.projection function) x (xs function) xs
          hx (projectionValue function xs)) (fun j => Fin.elim0 j))))) i

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterInputQueriesProof
