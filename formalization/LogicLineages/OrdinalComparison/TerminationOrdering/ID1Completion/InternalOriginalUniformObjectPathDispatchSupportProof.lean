module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformObjectPathDispatchTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformObjectPathDispatchSupportProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformObjectPathDispatch
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalEqualityTestCompositionProof
open SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

theorem windowAccept (window : Nat) (xs : Fin 5 → OTerm α)
    (h : Nonempty (Derivation body Delta (equal (xs 0) (numeral window)))) :
    Nonempty (Derivation body Delta (programGraph (windowTest window) (suc z) xs)) := by
  apply binaryValue InternalEqualityTest.equalityTest (.projection 0)
    (InternalCanonicalFixedWindowVertexDispatch.constant 5 window)
    (suc z) (xs 0) (numeral window) xs
  · apply equalityOfEqual
    simpa only [equalEqn] using h
  · exact projectionValue 0 xs
  · exact InternalCanonicalFixedWindowVertexDispatchSupportProof.constantValue 5 window xs

/-- The symbolic parameter is the output of the actual original pairing
AST on the context and actual left coordinate of this argument Object. -/
theorem runtimeParameterValue (xs : Fin 5 → OTerm α) (gammaCode parameter : OTerm α)
    (hl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode (xs 3))))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter (xs 0) gammaCode))) :
    Nonempty (Derivation body Delta (programGraph runtimeParameter parameter xs)) :=
  binaryValue InternalPairing.pairing (.projection 0) (leftOf (.projection 3))
    parameter (xs 0) gammaCode xs hp (projectionValue 0 xs)
    (unaryValue InternalUnpair.left (.projection 3) gammaCode (xs 3) xs hl (projectionValue 3 xs))

theorem activeInputs (xs : Fin 5 → OTerm α) (gammaCode argument parameter : OTerm α)
    (hc : Nonempty (Derivation body Delta (objectCoordinates gammaCode (xs 3) argument)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter (xs 0) gammaCode))) :
    ∀ i : Fin 5, Nonempty (Derivation body Delta
      (programGraph ((![Program.projection 4,runtimeParameter,.projection 1,.projection 2,
          rightOf (.projection 3)] : Fin 5 → Program 5) i)
        ((Fin.cons (xs 4) (Fin.cons parameter (Fin.cons (xs 1)
          (Fin.cons (xs 2) (Fin.cons argument Fin.elim0)))) : Fin 5 → OTerm α) i) xs)) := by
  intro i
  exact Fin.cases (projectionValue 4 xs)
    (Fin.cases (runtimeParameterValue xs gammaCode parameter (andLeft hc) hp)
      (Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 2 xs)
        (Fin.cases (unaryValue InternalUnpair.right (.projection 3) argument (xs 3) xs
          (andRight hc) (projectionValue 3 xs)) (fun j => Fin.elim0 j))))) i

theorem activeBranchRecover (vertexProgram : Program 5) (xs : Fin 5 → OTerm α)
    (gammaCode argument parameter out : OTerm α)
    (hc : Nonempty (Derivation body Delta (objectCoordinates gammaCode (xs 3) argument)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter (xs 0) gammaCode)))
    (h : Nonempty (Derivation body Delta (programGraph (activeBranch vertexProgram) out xs))) :
    Nonempty (Derivation body Delta
      (InternalApplicationPathMap.mapGraph vertexProgram out (xs 4) parameter (xs 1) (xs 2) argument)) :=
  compositionRecover (InternalApplicationPathMap.pathMap vertexProgram)
    ![.projection 4,runtimeParameter,.projection 1,.projection 2,rightOf (.projection 3)]
    out xs (Fin.cons (xs 4) (Fin.cons parameter (Fin.cons (xs 1)
      (Fin.cons (xs 2) (Fin.cons argument Fin.elim0))))) h (activeInputs xs gammaCode argument parameter hc hp)

theorem activeBranchAccept (vertexProgram : Program 5) (xs : Fin 5 → OTerm α)
    (gammaCode argument parameter out : OTerm α)
    (hc : Nonempty (Derivation body Delta (objectCoordinates gammaCode (xs 3) argument)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter (xs 0) gammaCode)))
    (h : Nonempty (Derivation body Delta
      (InternalApplicationPathMap.mapGraph vertexProgram out (xs 4) parameter (xs 1) (xs 2) argument))) :
    Nonempty (Derivation body Delta (programGraph (activeBranch vertexProgram) out xs)) :=
  compositionValue (InternalApplicationPathMap.pathMap vertexProgram)
    ![.projection 4,runtimeParameter,.projection 1,.projection 2,rightOf (.projection 3)]
    out xs (Fin.cons (xs 4) (Fin.cons parameter (Fin.cons (xs 1)
      (Fin.cons (xs 2) (Fin.cons argument Fin.elim0))))) h (activeInputs xs gammaCode argument parameter hc hp)

theorem dispatchRecover (window : Nat) (vertexProgram oldLift : Program 5)
    (context domain codomain gammaCode argumentObject argument parameter certificate out : OTerm α)
    (ha : Nonempty (Derivation body Delta
      (activePremises window context gammaCode argumentObject argument parameter)))
    (h : Nonempty (Derivation body Delta
      (dispatchGraph window vertexProgram oldLift out context domain codomain argumentObject certificate))) :
    Nonempty (Derivation body Delta
      (InternalApplicationPathMap.mapGraph vertexProgram out certificate parameter domain codomain argument)) := by
  let xs := arguments context domain codomain argumentObject certificate
  exact activeBranchRecover vertexProgram xs gammaCode argument parameter out
    (andLeft (andRight ha)) (andRight (andRight ha))
    (successorBranchElim (windowTest window) oldLift (activeBranch vertexProgram) out z xs
      (windowAccept window xs (andLeft ha)) h)

theorem dispatchAccept (window : Nat) (vertexProgram oldLift : Program 5)
    (context domain codomain gammaCode argumentObject argument parameter certificate out : OTerm α)
    (ha : Nonempty (Derivation body Delta
      (activePremises window context gammaCode argumentObject argument parameter)))
    (h : Nonempty (Derivation body Delta
      (InternalApplicationPathMap.mapGraph vertexProgram out certificate parameter domain codomain argument))) :
    Nonempty (Derivation body Delta
      (dispatchGraph window vertexProgram oldLift out context domain codomain argumentObject certificate)) := by
  let xs := arguments context domain codomain argumentObject certificate
  exact successorBranchIntro (windowTest window) oldLift (activeBranch vertexProgram) out z xs
    (windowAccept window xs (andLeft ha))
    (activeBranchAccept vertexProgram xs gammaCode argument parameter out
      (andLeft (andRight ha)) (andRight (andRight ha)) h)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformObjectPathDispatchSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformObjectPathDispatchSupportProof
