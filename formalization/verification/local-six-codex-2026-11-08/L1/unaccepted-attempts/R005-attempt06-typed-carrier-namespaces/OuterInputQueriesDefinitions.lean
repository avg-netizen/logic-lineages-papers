module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSelectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterInputQueries
open Source InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Proof-local totality queries on [function,targetFunction,RAWargument].
They are not additional selected source Programs or certificate fields. -/
def parameter (context : Nat) : Program 3 :=
  Outer.parameter (Path.constant 3 context) (.projection 0)

def rawVertex (data : Data) (window : Program 1) (oldVertex : Program 5)
    (context : Nat) (sigma tau : Ty) (function : Fin 3) : Program 3 :=
  .composition (Path.vertex data window oldVertex)
    (Fin.cons (parameter context) (Fin.cons (Path.constant 3 (typeNumber sigma))
      (Fin.cons (Path.constant 3 (typeNumber tau))
        (Fin.cons (rightOf (.projection 2)) (Fin.cons (rightOf (.projection function)) Fin.elim0)))))

def queries (data : Data) (window : Program 1) (oldVertex : Program 5)
    (context : Nat) (sigma tau : Ty) : Fin 7 → Program 3 :=
  Fin.cons (leftOf (.projection 0))
    (Fin.cons (rightOf (.projection 0))
      (Fin.cons (rightOf (.projection 1))
        (Fin.cons (rightOf (.projection 2))
          (Fin.cons (parameter context)
            (Fin.cons (rawVertex data window oldVertex context sigma tau 0)
              (Fin.cons (rawVertex data window oldVertex context sigma tau 1) Fin.elim0))))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterInputQueries
