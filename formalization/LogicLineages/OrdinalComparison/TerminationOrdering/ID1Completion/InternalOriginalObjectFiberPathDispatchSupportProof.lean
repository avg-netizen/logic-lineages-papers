module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchSupportProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalObjectFiberPathDispatch InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalGraphCompositionFunctionalityProof InternalControlGraphSupportProof
open InternalPositiveUnfoldingSupportProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalEqualityTestCompositionProof InternalEqualityTestProof
open InternalTagArithmeticSupportProof InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open InternalQuotientComparisonProof InternalBetaTotalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- Trichotomy is an internal theorem. Neither standard evaluation nor
decoder truth is used to derive rejection at the exact output zero. -/
theorem equalityOfNonmatch (x y : OTerm α)
    (hn : Nonempty (Derivation body Delta (eqn x y).not)) :
    Nonempty (Derivation body Delta (equalityGraph z x y)) := by
  obtain ⟨hn⟩ := hn
  obtain ⟨cmp⟩ := actualOriginalComparison body α x y
  have hc := compareView (weakenClosed cmp Delta)
  obtain ⟨hl⟩ := rejectForwardOrder (body := body) (Gamma := ltF x y :: Delta) x y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := rejectBackwardOrder (body := body) (Gamma := ltF y x :: Delta) x y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have he : Derivation body Delta ((eqn x y).imp (equalityGraph z x y)) :=
    Derivation.implicationIntroduction (Derivation.explosion
      (Derivation.implicationElimination (addHyp hn _) (Derivation.hypothesis List.mem_cons_self)))
  have hrest : Derivation body Delta ((eqn x y ⊔ ltF y x).imp (equalityGraph z x y)) :=
    Derivation.implicationIntroduction (disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (addHyp he _) (addHyp (Derivation.implicationIntroduction hr) _))
  exact ⟨disjunctionElimination hc (Derivation.implicationIntroduction hl) hrest⟩

theorem fiberTestAccept (Gamma : List Ty) (xs : Fin 5 → OTerm α)
    (hl : Nonempty (Derivation body Delta
      (graph1 InternalUnpair.left (numeral (Encodable.encode Gamma)) (xs 3)))) :
    Nonempty (Derivation body Delta (programGraph (fiberTest Gamma) (suc z) xs)) :=
  sameAccept (leftOf (.projection 3))
    (InternalCanonicalFixedWindowVertexDispatch.constant 5 (Encodable.encode Gamma))
    (numeral (Encodable.encode Gamma)) xs
    (unaryValue InternalUnpair.left (.projection 3) (numeral (Encodable.encode Gamma))
      (xs 3) xs hl (projectionValue 3 xs))
    (InternalCanonicalFixedWindowVertexDispatchSupportProof.constantValue 5 (Encodable.encode Gamma) xs)

theorem fiberTestReject (Gamma : List Ty) (xs : Fin 5 → OTerm α) (leftCode : OTerm α)
    (hl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left leftCode (xs 3))))
    (hn : Nonempty (Derivation body Delta
      (InternalControlGraph.equal leftCode (numeral (Encodable.encode Gamma))).not)) :
    Nonempty (Derivation body Delta (programGraph (fiberTest Gamma) z xs)) := by
  apply binaryValue InternalEqualityTest.equalityTest (leftOf (.projection 3))
    (InternalCanonicalFixedWindowVertexDispatch.constant 5 (Encodable.encode Gamma))
    z leftCode (numeral (Encodable.encode Gamma)) xs
  · apply equalityOfNonmatch
    simpa only [equalEqn] using hn
  · exact unaryValue InternalUnpair.left (.projection 3) leftCode (xs 3) xs hl (projectionValue 3 xs)
  · exact InternalCanonicalFixedWindowVertexDispatchSupportProof.constantValue 5 (Encodable.encode Gamma) xs

theorem activeInputs (xs : Fin 5 → OTerm α) (argument : OTerm α)
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right argument (xs 3)))) :
    ∀ i : Fin 5, Nonempty (Derivation body Delta
      (programGraph ((![Program.projection 4,.projection 0,.projection 1,.projection 2,
          rightOf (.projection 3)] : Fin 5 → Program 5) i)
        ((Fin.cons (xs 4) (Fin.cons (xs 0) (Fin.cons (xs 1)
          (Fin.cons (xs 2) (Fin.cons argument Fin.elim0)))) : Fin 5 → OTerm α) i) xs)) := by
  intro i
  exact Fin.cases (projectionValue 4 xs) (Fin.cases (projectionValue 0 xs)
    (Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 2 xs)
      (Fin.cases (unaryValue InternalUnpair.right (.projection 3) argument (xs 3) xs hr
        (projectionValue 3 xs)) (fun j => Fin.elim0 j))))) i

theorem activeBranchRecover (vertexProgram : Program 5) (xs : Fin 5 → OTerm α)
    (argument out : OTerm α)
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right argument (xs 3))))
    (h : Nonempty (Derivation body Delta (programGraph (activeBranch vertexProgram) out xs))) :
    Nonempty (Derivation body Delta
      (InternalApplicationPathMap.mapGraph vertexProgram out (xs 4) (xs 0) (xs 1) (xs 2) argument)) :=
  compositionRecover (InternalApplicationPathMap.pathMap vertexProgram)
    ![.projection 4,.projection 0,.projection 1,.projection 2,rightOf (.projection 3)]
    out xs (Fin.cons (xs 4) (Fin.cons (xs 0) (Fin.cons (xs 1)
      (Fin.cons (xs 2) (Fin.cons argument Fin.elim0))))) h (activeInputs xs argument hr)

theorem activeBranchAccept (vertexProgram : Program 5) (xs : Fin 5 → OTerm α)
    (argument out : OTerm α)
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right argument (xs 3))))
    (h : Nonempty (Derivation body Delta
      (InternalApplicationPathMap.mapGraph vertexProgram out (xs 4) (xs 0) (xs 1) (xs 2) argument))) :
    Nonempty (Derivation body Delta (programGraph (activeBranch vertexProgram) out xs)) :=
  compositionValue (InternalApplicationPathMap.pathMap vertexProgram)
    ![.projection 4,.projection 0,.projection 1,.projection 2,rightOf (.projection 3)]
    out xs (Fin.cons (xs 4) (Fin.cons (xs 0) (Fin.cons (xs 1)
      (Fin.cons (xs 2) (Fin.cons argument Fin.elim0))))) h (activeInputs xs argument hr)

theorem dispatchRecover (Gamma : List Ty) (vertexProgram oldLift : Program 5)
    (context domain codomain argumentObject argument certificate out : OTerm α)
    (hf : Nonempty (Derivation body Delta (fiberCoordinates Gamma argumentObject argument)))
    (h : Nonempty (Derivation body Delta
      (dispatchGraph Gamma vertexProgram oldLift out context domain codomain argumentObject certificate))) :
    Nonempty (Derivation body Delta
      (InternalApplicationPathMap.mapGraph vertexProgram out certificate context domain codomain argument)) := by
  let xs := arguments context domain codomain argumentObject certificate
  exact activeBranchRecover vertexProgram xs argument out (andRight hf)
    (successorBranchElim (fiberTest Gamma) oldLift (activeBranch vertexProgram) out z xs
      (fiberTestAccept Gamma xs (andLeft hf)) h)

theorem dispatchAccept (Gamma : List Ty) (vertexProgram oldLift : Program 5)
    (context domain codomain argumentObject argument certificate out : OTerm α)
    (hf : Nonempty (Derivation body Delta (fiberCoordinates Gamma argumentObject argument)))
    (h : Nonempty (Derivation body Delta
      (InternalApplicationPathMap.mapGraph vertexProgram out certificate context domain codomain argument))) :
    Nonempty (Derivation body Delta
      (dispatchGraph Gamma vertexProgram oldLift out context domain codomain argumentObject certificate)) := by
  let xs := arguments context domain codomain argumentObject certificate
  exact successorBranchIntro (fiberTest Gamma) oldLift (activeBranch vertexProgram) out z xs
    (fiberTestAccept Gamma xs (andLeft hf))
    (activeBranchAccept vertexProgram xs argument out (andRight hf) h)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchSupportProof
