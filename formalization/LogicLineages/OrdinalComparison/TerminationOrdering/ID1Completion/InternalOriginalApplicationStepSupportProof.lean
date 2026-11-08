module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepCheckerGraphProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalApplicationStep InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The actual outer pair in packedApplication forces its codomain tag.
Its intermediate payload is eliminated by original composition elimination. -/
theorem packedApplicationTag (out : OTerm α) (xs : Fin 4 → OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph packedApplication out xs))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left (xs 1) out)) := by
  apply programCompositionCases InternalPairing.pairing
    ![.projection 1,pairOf (two 4)
      (pairOf (.projection 0) (pairOf (.projection 2) (.projection 3)))] out xs _ h
  intro β j ys Delta _ hp hg
  rw [graph1Rename]
  have htuple : Fin.cons (ys 0) (Fin.cons (ys 1) Fin.elim0) = ys := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  have hpair : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing (out.relabel j) (ys 0) (ys 1))) := by
    simpa only [graph2,htuple] using hp
  have he := valueUnique (.projection (1 : Fin 4)) (ys 0) ((xs 1).relabel j)
    (fun i => (xs i).relabel j) (hg 0)
    (projectionValue 1 (fun i => (xs i).relabel j))
  exact outputTransport InternalUnpair.left (ys 0) ((xs 1).relabel j)
    (Fin.cons (out.relabel j) Fin.elim0) he (pairLeft _ _ _ hpair)

/-- Raw application has the same codomain tag even on arbitrary malformed
children. No child tag or successful decoder premise is required here. -/
theorem applicationTag (d e f a out : OTerm α)
    (h : Nonempty (Derivation body Gamma (graph4 application out d e f a))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left e out)) := by
  let xs : Fin 4 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons f (Fin.cons a Fin.elim0)))
  apply programCompositionCases packedApplication
    ![.projection 0,.projection 1,rightOf (.projection 2),rightOf (.projection 3)] out xs _ h
  intro β j ys Delta _ hp hg
  rw [graph1Rename]
  have he := valueUnique (.projection (1 : Fin 4)) (ys 1) (e.relabel j)
    (fun i => (xs i).relabel j) (hg 1)
    (projectionValue 1 (fun i => (xs i).relabel j))
  exact outputTransport InternalUnpair.left (ys 1) (e.relabel j)
    (Fin.cons (out.relabel j) Fin.elim0) he (packedApplicationTag _ ys hp)

/-- The checked recursive endpoint closure supplies both new validities.
The checked normalizer transports the actual core acceptance, and the two
original application tag graphs reconstruct the original outer guard. -/
theorem applicationStep (data : Data)
    (arrow d e s t a k sourceApp targetApp liftedStep : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (InternalOriginalApplicationStep.liftPremises data
        arrow d e s t a k sourceApp targetApp liftedStep)))
    (hs : Nonempty (Derivation body Gamma (accepted data s t k))) :
    Nonempty (Derivation body Gamma (accepted data sourceApp targetApp liftedStep)) := by
  have hendpointPremises := andLeft hp
  have har := andLeft hendpointPremises
  have hend := andLeft (andRight hendpointPremises)
  have hsourceApp := andLeft (andRight (andRight hendpointPremises))
  have htargetApp := andRight (andRight (andRight hendpointPremises))
  have hrequirements := InternalStructuralEndpointGuardSupportProof.endpointRecover
    (validity data) data.member arrow d e s t a har hend
  have htags := andLeft (andRight (andRight (andRight hrequirements)))
  have hcore := andRight (conjunctionRecover (InternalOriginalStepGuard.guards (validity data))
    (normalizedCore data) (Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))) hs)
  have hnormalizedPremises : Nonempty (Derivation body Gamma
      (InternalApplicationStepChecker.liftedCheckerPremises (endpoint data)
        d e arrow s t a k sourceApp targetApp liftedStep)) :=
    andIntro har (andIntro (andLeft htags)
      (andIntro (andLeft (andRight htags)) (andIntro (andRight (andRight htags))
        (andIntro hend (andIntro hsourceApp (andIntro htargetApp (andRight hp)))))))
  have hliftedCore := InternalApplicationStepCheckerGraphProof.checkerBackward
    (endpoint data) data.oldStep d e arrow s t a k sourceApp targetApp liftedStep
    InternalOriginalStepGuard.one hnormalizedPremises hcore
  have hvalidity := InternalRecursionClosureLogicProof.closedApply
    (InternalApplicationValidityClosureProof.actualOriginalRecursiveEndpointApplicationValidity
      body data.oldValidity data.member α arrow d e s t a sourceApp targetApp) hendpointPremises
  have hsame : Nonempty (Derivation body Gamma (equal e e)) := by
    rw [equalEqn]
    exact ⟨refl e⟩
  exact InternalOriginalStepGuardSupportProof.checkerAccept (validity data) (normalizedCore data)
    e e sourceApp targetApp liftedStep
    (andIntro (applicationTag d e s a sourceApp hsourceApp)
      (applicationTag d e t a targetApp htargetApp))
    (andIntro (andLeft hvalidity) (andIntro (andRight hvalidity)
      (andIntro hsame hliftedCore)))

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepSupportProof
