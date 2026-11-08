module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeTypeGuardTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeTypeGuardSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalQuotientEdgeTypeGuard InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem sourceTypeValue (typ : OTerm α) (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation body Gamma (sourceTypeGraph typ (xs 0)))) :
    Nonempty (Derivation body Gamma (programGraph sourceType typ xs)) :=
  unaryValue InternalUnpair.left (.projection 0) typ (xs 0) xs h (projectionValue 0 xs)

theorem typedAtAccept (typedProgram : Program 2) (endpoint : Fin 3)
    (typ : OTerm α) (xs : Fin 3 → OTerm α)
    (htag : Nonempty (Derivation body Gamma (sourceTypeGraph typ (xs 0))))
    (htyped : Nonempty (Derivation body Gamma (typed typedProgram (xs endpoint) typ))) :
    Nonempty (Derivation body Gamma (programGraph (typedAt typedProgram endpoint) (suc z) xs)) :=
  binaryValue typedProgram (.projection endpoint) sourceType (suc z) (xs endpoint) typ xs
    htyped (projectionValue endpoint xs) (sourceTypeValue typ xs htag)

theorem typedAtRecover (typedProgram : Program 2) (endpoint : Fin 3)
    (typ : OTerm α) (xs : Fin 3 → OTerm α)
    (htag : Nonempty (Derivation body Gamma (sourceTypeGraph typ (xs 0))))
    (htyped : Nonempty (Derivation body Gamma
      (programGraph (typedAt typedProgram endpoint) (suc z) xs))) :
    Nonempty (Derivation body Gamma (typed typedProgram (xs endpoint) typ)) :=
  binaryRecover typedProgram (.projection endpoint) sourceType (suc z) (xs endpoint) typ xs
    htyped (projectionValue endpoint xs) (sourceTypeValue typ xs htag)

theorem checkerRecover (data : InternalQuotientEdgeChecker.Data) (typedProgram : Program 2)
    (x y certificate typ : OTerm α)
    (htag : Nonempty (Derivation body Gamma (sourceTypeGraph typ x)))
    (hedge : Nonempty (Derivation body Gamma (accepted data typedProgram x y certificate))) :
    Nonempty (Derivation body Gamma (requirements data typedProgram x y certificate typ)) := by
  let xs : Fin 3 → OTerm α := Fin.cons x (Fin.cons y (Fin.cons certificate Fin.elim0))
  have houter := conjunctionRecover (InternalQuotientEdgeChecker.checker data)
    (InternalAcceptance.conjunction (typedAt typedProgram 0) (typedAt typedProgram 1)) xs hedge
  have hinner := conjunctionRecover (typedAt typedProgram 0) (typedAt typedProgram 1)
    xs (andRight houter)
  exact andIntro (andLeft houter)
    (andIntro (typedAtRecover typedProgram 0 typ xs htag (andLeft hinner))
      (typedAtRecover typedProgram 1 typ xs htag (andRight hinner)))

theorem checkerAccept (data : InternalQuotientEdgeChecker.Data) (typedProgram : Program 2)
    (x y certificate typ : OTerm α)
    (htag : Nonempty (Derivation body Gamma (sourceTypeGraph typ x)))
    (hreq : Nonempty (Derivation body Gamma (requirements data typedProgram x y certificate typ))) :
    Nonempty (Derivation body Gamma (accepted data typedProgram x y certificate)) := by
  let xs : Fin 3 → OTerm α := Fin.cons x (Fin.cons y (Fin.cons certificate Fin.elim0))
  exact conjunctionAccept (InternalQuotientEdgeChecker.checker data)
    (InternalAcceptance.conjunction (typedAt typedProgram 0) (typedAt typedProgram 1)) xs
    (andLeft hreq)
    (conjunctionAccept (typedAt typedProgram 0) (typedAt typedProgram 1) xs
      (typedAtAccept typedProgram 0 typ xs htag (andLeft (andRight hreq)))
      (typedAtAccept typedProgram 1 typ xs htag (andRight (andRight hreq))))

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeTypeGuardSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeTypeGuardSupportProof
