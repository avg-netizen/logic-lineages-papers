module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalParameterizedStructuralEndpointGuard
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeelComponentsProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem atValue (P : Program 2) (i : Fin 6) (out : OTerm α) (xs : Fin 6 → OTerm α)
    (h : Nonempty (Derivation body Gamma (graph2 P out (xs i) (xs 5)))) :
    Nonempty (Derivation body Gamma (programGraph (atParameter P i) out xs)) :=
  binaryValue P (.projection i) (.projection 5) out (xs i) (xs 5) xs h
    (projectionValue i xs) (projectionValue 5 xs)

theorem atRecover (P : Program 2) (i : Fin 6) (out : OTerm α) (xs : Fin 6 → OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph (atParameter P i) out xs))) :
    Nonempty (Derivation body Gamma (graph2 P out (xs i) (xs 5))) :=
  binaryRecover P (.projection i) (.projection 5) out (xs i) (xs 5) xs h
    (projectionValue i xs) (projectionValue 5 xs)

theorem typeRecover (arrow d e s t a parameter : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (h : Nonempty (Derivation body Gamma (graph6 typeGuard (suc z) d e s t a parameter))) :
    Nonempty (Derivation body Gamma (InternalStructuralEndpointGuard.tagGraphs arrow d s t a)) := by
  let xs : Fin 6 → OTerm α := ![d,e,s,t,a,parameter]
  have hv : Nonempty (Derivation body Gamma
      (InternalApplicationStepPeel.graph5 InternalApplicationStepPeel.endpointTypeGuard (suc z) d e s t a)) := by
    apply compositionRecover InternalApplicationStepPeel.endpointTypeGuard
      ![.projection 0,.projection 1,.projection 2,.projection 3,.projection 4]
      (suc z) xs ![d,e,s,t,a] h
    intro i
    exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
      (Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs)
        (Fin.cases (projectionValue 4 xs) (fun k => Fin.elim0 k))))) i
  exact InternalStructuralEndpointGuardSupportProof.typeGuardRecover arrow d e s t a har hv

theorem typeValue (arrow d e s t a parameter : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (h : Nonempty (Derivation body Gamma (InternalStructuralEndpointGuard.tagGraphs arrow d s t a))) :
    Nonempty (Derivation body Gamma (graph6 typeGuard (suc z) d e s t a parameter)) := by
  let xs : Fin 6 → OTerm α := ![d,e,s,t,a,parameter]
  have hv := endpointTypesAccept d e arrow s t a har (andLeft h)
    (andLeft (andRight h)) (andRight (andRight h))
  apply compositionValue InternalApplicationStepPeel.endpointTypeGuard
    ![.projection 0,.projection 1,.projection 2,.projection 3,.projection 4]
    (suc z) xs ![d,e,s,t,a] hv
  intro i
  exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
    (Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs)
      (Fin.cases (projectionValue 4 xs) (fun k => Fin.elim0 k))))) i

/-- Every accepted coordinate is an actual graph at the unchanged symbolic
parameter. The packed-target factor remains separate from source validity. -/
theorem endpointRecover (sourceValid targetValid member : Program 2)
    (arrow d e s t a parameter : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (h : Nonempty (Derivation body Gamma (accepted sourceValid targetValid member d e s t a parameter))) :
    Nonempty (Derivation body Gamma
      (requirements sourceValid targetValid member arrow d e s t a parameter)) := by
  let xs : Fin 6 → OTerm α := ![d,e,s,t,a,parameter]
  have hsource := conjunctionRecover _ _ xs h
  have htarget := conjunctionRecover _ _ xs (andRight hsource)
  have hargument := conjunctionRecover _ _ xs (andRight htarget)
  have htail := conjunctionRecover _ _ xs (andRight hargument)
  exact andIntro (atRecover sourceValid 2 (suc z) xs (andLeft hsource))
    (andIntro (atRecover targetValid 3 (suc z) xs (andLeft htarget))
      (andIntro (atRecover sourceValid 4 (suc z) xs (andLeft hargument))
        (andIntro (typeRecover arrow d e s t a parameter har (andLeft htail))
          (atRecover member 1 (suc z) xs (andRight htail)))))

theorem endpointAccept (sourceValid targetValid member : Program 2)
    (arrow d e s t a parameter : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (h : Nonempty (Derivation body Gamma
      (requirements sourceValid targetValid member arrow d e s t a parameter))) :
    Nonempty (Derivation body Gamma (accepted sourceValid targetValid member d e s t a parameter)) := by
  let xs : Fin 6 → OTerm α := ![d,e,s,t,a,parameter]
  have hs := andLeft h
  have ht := andLeft (andRight h)
  have ha := andLeft (andRight (andRight h))
  have htail := andRight (andRight (andRight h))
  apply conjunctionAccept _ _ xs (atValue sourceValid 2 (suc z) xs hs)
  apply conjunctionAccept _ _ xs (atValue targetValid 3 (suc z) xs ht)
  apply conjunctionAccept _ _ xs (atValue sourceValid 4 (suc z) xs ha)
  exact conjunctionAccept _ _ xs (typeValue arrow d e s t a parameter har (andLeft htail))
    (atValue member 1 (suc z) xs (andRight htail))

theorem actualParameterizedEndpointAcceptanceAtArrow :
    InternalParameterizedStructuralEndpointGuardTargets.ActualParameterizedEndpointAcceptanceAtArrow := by
  intro body sourceValid targetValid member α Delta arrow d e s t a parameter
  let A := graph2 InternalListCodec.consCode arrow d e
  let P := accepted sourceValid targetValid member d e s t a parameter
  let Q := requirements sourceValid targetValid member arrow d e s t a parameter
  obtain ⟨hf⟩ := endpointRecover (body := body) (Gamma := P :: A :: Delta)
    sourceValid targetValid member arrow d e s t a parameter
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := endpointAccept (body := body) (Gamma := Q :: A :: Delta)
    sourceValid targetValid member arrow d e s t a parameter
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardSupportProof
