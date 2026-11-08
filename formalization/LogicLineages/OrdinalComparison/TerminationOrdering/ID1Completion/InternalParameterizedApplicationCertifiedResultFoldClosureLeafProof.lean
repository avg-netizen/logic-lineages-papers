module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosurePreflight
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldLeafClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureBridgeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionFrameConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionFrameSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalGraphComposition
open InternalApplicationCertificateConstructors InternalApplicationCertifiedResultFoldClosure
open InternalParameterizedApplicationCertifiedResultFoldClosure InternalApplicationResultStackComposition
open InternalApplicationCertifiedResultFoldLeafClosureProof (queries visitQ workQ singletonQ initialQ terminalQ payloadQ)
open InternalParameterizedApplicationCertifiedResultFoldClosureSyntaxProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalParameterizedApplicationCertifiedResultFoldClosureBridgeProof
open InternalApplicationCertifiedResultFoldClosureBridgeStateProof
open InternalParameterizedApplicationResultStackCompositionFrameSupportProof
open InternalParameterizedApplicationResultStackCompositionBasicProof InternalParameterizedApplicationResultStackCompositionStepProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel)
open InternalAcceptanceConjunctionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem leafFromQueries (guard leaf : Program 2) (combine : Program 5)
    (value out parameter : OTerm α) (ys : Fin 6 → OTerm α)
    (hg : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP guard) z value parameter)))
    (hl : Nonempty (Derivation body Gamma (graph2 leaf out value parameter)))
    (hq : ∀ i, Nonempty (Derivation body Gamma
      (programGraph (queries i) (ys i) (Fin.cons value (Fin.cons out Fin.elim0))))) :
    Nonempty (Derivation body Gamma (certifiedFoldP guard leaf combine out value parameter)) := by
  let xs : Fin 2 → OTerm α := Fin.cons value (Fin.cons out Fin.elim0)
  have hv := binaryRecover InternalPairing.pairing (InternalAcceptance.constantZero 2) (.projection 0)
    (ys 0) z value xs (hq 0) (constantZeroValue xs) (projectionValue 0 xs)
  have hw := binaryRecover InternalListCodec.consCode visitQ (InternalAcceptance.constantZero 2)
    (ys 1) (ys 0) z xs (hq 1) (hq 0) (constantZeroValue xs)
  have hc := binaryRecover InternalListCodec.consCode (.projection 1) (InternalAcceptance.constantZero 2)
    (ys 2) out z xs (hq 2) (projectionValue 1 xs) (constantZeroValue xs)
  have hi := binaryRecover liveState workQ (InternalAcceptance.constantZero 2)
    (ys 3) (ys 1) z xs (hq 3) (hq 1) (constantZeroValue xs)
  have he := binaryRecover liveState (InternalAcceptance.constantZero 2) singletonQ
    (ys 4) z (ys 2) xs (hq 4) (constantZeroValue xs) (hq 2)
  have hp := unaryRecover InternalUnpair.right (.projection 0) (ys 5) value xs
    (hq 5) (projectionValue 0 xs)
  have ht := leafTransitionAt guard leaf combine parameter (ys 3) (ys 1) z (ys 0) value z
    (ys 4) out (ys 2) hi hw hv hg hl hc he
  have hr := runFrontBackward guard leaf combine parameter (OrdinaryArithmetic.addTerm (ys 5) (ys 5))
    (ys 1) z (ys 2) (ys 3) z (ys 2) (ys 4) hi he ht
    (emptyRun guard leaf combine parameter (OrdinaryArithmetic.addTerm (ys 5) (ys 5)) (ys 2))
  let unary : Fin 1 → OTerm α := Fin.cons value Fin.elim0
  have hvisit := binaryValue InternalPairing.pairing (InternalAcceptance.constantZero 1)
    (.projection 0) (ys 0) z value unary hv (constantZeroValue unary) (projectionValue 0 unary)
  have hwork : Nonempty (Derivation body Gamma (graph1 visitWork (ys 1) value)) :=
    binaryValue InternalListCodec.consCode (InternalApplicationResultStack.visitOf (.projection 0))
      (InternalAcceptance.constantZero 1) (ys 1) (ys 0) z unary hw hvisit (constantZeroValue unary)
  exact certifiedFoldOfRun guard leaf combine value (ys 5) (ys 1) out (ys 2) parameter hp hwork hc hr

/-- Context-uniform continuation consuming only the two actual branch graphs. -/
theorem leafClosure (guard leaf : Program 2) (combine : Program 5)
    (value out parameter : OTerm α)
    (hg : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP guard) z value parameter)))
    (hl : Nonempty (Derivation body Gamma (graph2 leaf out value parameter))) :
    Nonempty (Derivation body Gamma (certifiedFoldP guard leaf combine out value parameter)) := by
  apply queryCases queries (Fin.cons value (Fin.cons out Fin.elim0)) _
  intro β j ys Delta hj hq
  rw [certifiedFoldPRename]
  have hg' := renameInto hg j Delta hj
  have hl' := renameInto hl j Delta hj
  simp only [graph2Rename,zRelabel] at hg' hl'
  simp only [consTermRename,emptyRename] at hq
  exact leafFromQueries guard leaf combine (value.relabel j) (out.relabel j) (parameter.relabel j) ys hg' hl' hq

theorem actualOriginalParameterizedCertifiedResultFoldLeafClosure :
    InternalParameterizedApplicationCertifiedResultFoldClosureTargets.ActualOriginalParameterizedCertifiedResultFoldLeafClosure := by
  intro body guard leaf combine α Gamma value out parameter
  have h : Nonempty (Derivation body (leafGraphsP guard leaf out value parameter :: Gamma)
      (leafGraphsP guard leaf out value parameter)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨result⟩ := leafClosure guard leaf combine value out parameter (andLeft h) (andRight h)
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureLeafProof
