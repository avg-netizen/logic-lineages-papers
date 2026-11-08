module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelComponentsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalStructuralEndpointGuard
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeelComponentsProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalEqualityTestProof InternalTagArithmeticSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Internal totality supplies the unknown left output; accepted equality
transports its actual graph to the known right output. -/
 theorem sameRightRecover {n : Nat} (p q : Program n) (value : OTerm α)
    (xs : Fin n → OTerm α)
    (he : Nonempty (Derivation body Gamma
      (programGraph (InternalApplicationStepPeel.same p q) (suc z) xs)))
    (hq : Nonempty (Derivation body Gamma (programGraph q value xs))) :
    Nonempty (Derivation body Gamma (programGraph p value xs)) := by
  apply programCases p xs _
  intro β j Delta left hj hl
  simp only [programRename]
  have he' := renameInto he j Delta hj
  have hq' := renameInto hq j Delta hj
  simp only [programRename,sucRelabel,zRelabel] at he' hq'
  have hEq := equalityOfAcceptance left (value.relabel j)
    (binaryRecover InternalEqualityTest.equalityTest p q (suc z) left (value.relabel j)
      (fun i => (xs i).relabel j) he' hl hq')
  exact outputTransport p left (value.relabel j) (fun i => (xs i).relabel j) hEq hl

 theorem atValue (p : Program 1) (i : Fin 5) (out : OTerm α) (xs : Fin 5 → OTerm α)
    (h : Nonempty (Derivation body Gamma (graph1 p out (xs i)))) :
    Nonempty (Derivation body Gamma
      (programGraph (.composition p (fun _ : Fin 1 => .projection i)) out xs)) :=
  unaryValue p (.projection i) out (xs i) xs h (projectionValue i xs)

 theorem atRecover (p : Program 1) (i : Fin 5) (out : OTerm α) (xs : Fin 5 → OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph (.composition p (fun _ : Fin 1 => .projection i)) out xs))) :
    Nonempty (Derivation body Gamma (graph1 p out (xs i))) :=
  unaryRecover p (.projection i) out (xs i) xs h (projectionValue i xs)

 theorem typeGuardRecover (arrow d e s t a : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (h : Nonempty (Derivation body Gamma
      (InternalApplicationStepPeel.graph5 InternalApplicationStepPeel.endpointTypeGuard (suc z) d e s t a))) :
    Nonempty (Derivation body Gamma (tagGraphs arrow d s t a)) := by
  let xs : Fin 5 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons s (Fin.cons t (Fin.cons a Fin.elim0))))
  have har' := binaryValue InternalListCodec.consCode (.projection 0) (.projection 1)
    arrow d e xs har (projectionValue 0 xs) (projectionValue 1 xs)
  have htop := conjunctionRecover _ _ xs h
  have hinner := conjunctionRecover _ _ xs (andRight htop)
  have hs := sameRightRecover (leftOf (.projection 2)) (consOf (.projection 0) (.projection 1))
    arrow xs (andLeft htop) har'
  have ht := sameRightRecover (leftOf (.projection 3)) (consOf (.projection 0) (.projection 1))
    arrow xs (andLeft hinner) har'
  have ha := sameRightRecover (leftOf (.projection 4)) (.projection 0)
    d xs (andRight hinner) (projectionValue 0 xs)
  exact andIntro (atRecover InternalUnpair.left 2 arrow xs hs)
    (andIntro (atRecover InternalUnpair.left 3 arrow xs ht)
      (atRecover InternalUnpair.left 4 d xs ha))

 theorem endpointRecover (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (arrow d e s t a : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (h : Nonempty (Derivation body Gamma (accepted validity member d e s t a))) :
    Nonempty (Derivation body Gamma (requirements validity member arrow d e s t a)) := by
  let xs : Fin 5 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons s (Fin.cons t (Fin.cons a Fin.elim0))))
  have hsource := conjunctionRecover _ _ xs h
  have htarget := conjunctionRecover _ _ xs (andRight hsource)
  have hargument := conjunctionRecover _ _ xs (andRight htarget)
  have htail := conjunctionRecover _ _ xs (andRight hargument)
  exact andIntro (atRecover validity.sourceValid 2 (suc z) xs (andLeft hsource))
    (andIntro (atRecover validity.targetValid 3 (suc z) xs (andLeft htarget))
      (andIntro (atRecover validity.sourceValid 4 (suc z) xs (andLeft hargument))
        (andIntro (typeGuardRecover arrow d e s t a har (andLeft htail))
          (atRecover member 1 (suc z) xs (andRight htail)))))

 theorem endpointAccept (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (arrow d e s t a : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (h : Nonempty (Derivation body Gamma (requirements validity member arrow d e s t a))) :
    Nonempty (Derivation body Gamma (accepted validity member d e s t a)) := by
  let xs : Fin 5 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons s (Fin.cons t (Fin.cons a Fin.elim0))))
  have hs := andLeft h
  have ht := andLeft (andRight h)
  have ha := andLeft (andRight (andRight h))
  have htail := andRight (andRight (andRight h))
  have htags := andLeft htail
  apply conjunctionAccept _ _ xs (atValue validity.sourceValid 2 (suc z) xs hs)
  apply conjunctionAccept _ _ xs (atValue validity.targetValid 3 (suc z) xs ht)
  apply conjunctionAccept _ _ xs (atValue validity.sourceValid 4 (suc z) xs ha)
  exact conjunctionAccept _ _ xs
    (endpointTypesAccept d e arrow s t a har (andLeft htags)
      (andLeft (andRight htags)) (andRight (andRight htags)))
    (atValue member 1 (suc z) xs (andRight htail))

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardSupportProof
