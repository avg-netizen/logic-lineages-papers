module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerTypedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalParameterizedQuotientEdgeChecker
open InternalOriginalUniformDescentSelection (Data validity selectedTyped)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem sourceTypeValue (typ : OTerm α) (xs : Fin 4 → OTerm α)
    (h : Nonempty (Derivation body Gamma (sourceTypeGraph typ (xs 0)))) :
    Nonempty (Derivation body Gamma (programGraph sourceType typ xs)) :=
  unaryValue InternalUnpair.left (.projection 0) typ (xs 0) xs h (projectionValue 0 xs)

theorem typedComponents (endpoint : Fin 4) (typ : OTerm α) (xs : Fin 4 → OTerm α)
    (htag : Nonempty (Derivation body Gamma (sourceTypeGraph typ (xs 0)))) :
    ∀ i : Fin 3, Nonempty (Derivation body Gamma
      (programGraph ((![.projection endpoint,sourceType,.projection 3] : Fin 3 → Program 4) i)
        (![xs endpoint,typ,xs 3] i) xs)) := by
  intro i
  exact Fin.cases (projectionValue endpoint xs)
    (Fin.cases (sourceTypeValue typ xs htag)
      (Fin.cases (projectionValue 3 xs) (fun q => Fin.elim0 q))) i

theorem typedAtAccept (data : Data) (endpoint : Fin 4)
    (typ : OTerm α) (xs : Fin 4 → OTerm α)
    (htag : Nonempty (Derivation body Gamma (sourceTypeGraph typ (xs 0))))
    (htyped : Nonempty (Derivation body Gamma (typedAccepted data (xs endpoint) typ (xs 3)))) :
    Nonempty (Derivation body Gamma (programGraph (typedAt data endpoint) (suc z) xs)) :=
  compositionValue (selectedTyped data) ![.projection endpoint,sourceType,.projection 3]
    (suc z) xs ![xs endpoint,typ,xs 3] htyped (typedComponents endpoint typ xs htag)

theorem typedAtRecover (data : Data) (endpoint : Fin 4)
    (typ : OTerm α) (xs : Fin 4 → OTerm α)
    (htag : Nonempty (Derivation body Gamma (sourceTypeGraph typ (xs 0))))
    (htyped : Nonempty (Derivation body Gamma (programGraph (typedAt data endpoint) (suc z) xs))) :
    Nonempty (Derivation body Gamma (typedAccepted data (xs endpoint) typ (xs 3))) :=
  compositionRecover (selectedTyped data) ![.projection endpoint,sourceType,.projection 3]
    (suc z) xs ![xs endpoint,typ,xs 3] htyped (typedComponents endpoint typ xs htag)

theorem acceptedCore (data : Data) (oldStep : Program 4)
    (x y certificate parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (accepted data oldStep x y certificate parameter))) :
    Nonempty (Derivation body Gamma (coreAccepted data oldStep x y certificate parameter)) :=
  andLeft (conjunctionRecover (coreChecker data oldStep)
    (InternalAcceptance.conjunction (typedAt data 0) (typedAt data 1))
    (Fin.cons x (Fin.cons y (Fin.cons certificate (Fin.cons parameter Fin.elim0)))) h)

theorem wrapperRecover (data : Data) (oldStep : Program 4)
    (x y certificate typ parameter : OTerm α)
    (htag : Nonempty (Derivation body Gamma (sourceTypeGraph typ x)))
    (hedge : Nonempty (Derivation body Gamma (accepted data oldStep x y certificate parameter))) :
    Nonempty (Derivation body Gamma (typedRequirements data oldStep x y certificate typ parameter)) := by
  let xs : Fin 4 → OTerm α :=
    Fin.cons x (Fin.cons y (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  have houter := conjunctionRecover (coreChecker data oldStep)
    (InternalAcceptance.conjunction (typedAt data 0) (typedAt data 1)) xs hedge
  have hinner := conjunctionRecover (typedAt data 0) (typedAt data 1) xs (andRight houter)
  exact andIntro (andLeft houter)
    (andIntro (typedAtRecover data 0 typ xs htag (andLeft hinner))
      (typedAtRecover data 1 typ xs htag (andRight hinner)))

theorem wrapperAccept (data : Data) (oldStep : Program 4)
    (x y certificate typ parameter : OTerm α)
    (htag : Nonempty (Derivation body Gamma (sourceTypeGraph typ x)))
    (hreq : Nonempty (Derivation body Gamma (typedRequirements data oldStep x y certificate typ parameter))) :
    Nonempty (Derivation body Gamma (accepted data oldStep x y certificate parameter)) := by
  let xs : Fin 4 → OTerm α :=
    Fin.cons x (Fin.cons y (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  exact conjunctionAccept (coreChecker data oldStep)
    (InternalAcceptance.conjunction (typedAt data 0) (typedAt data 1)) xs (andLeft hreq)
    (conjunctionAccept (typedAt data 0) (typedAt data 1) xs
      (typedAtAccept data 0 typ xs htag (andLeft (andRight hreq)))
      (typedAtAccept data 1 typ xs htag (andRight (andRight hreq))))

/-- The selected typed checker internally exposes the requested raw tag. -/
theorem typedSourceTag (data : Data) (value typ parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (typedAccepted data value typ parameter))) :
    Nonempty (Derivation body Gamma (sourceTypeGraph typ value)) := by
  have hf := InternalOriginalUniformDescentSelectionInternalProof.typedRecover
    data.oldRepresentative (validity data) data.member value typ parameter h
  exact andLeft (andRight (andRight hf))

/-- Selected source typing identifies the actual tag used by the wrapper;
the target is consequently typed at the identical requested type and p. -/
theorem typedPropagation (data : Data) (oldStep : Program 4)
    (x y certificate typ parameter : OTerm α)
    (htyped : Nonempty (Derivation body Gamma (typedAccepted data x typ parameter)))
    (hedge : Nonempty (Derivation body Gamma (accepted data oldStep x y certificate parameter))) :
    Nonempty (Derivation body Gamma (typedAccepted data y typ parameter)) :=
  andRight (andRight (wrapperRecover data oldStep x y certificate typ parameter
    (typedSourceTag data x typ parameter htyped) hedge))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerTypedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerTypedProof
