module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldLeafClosurePreflight
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureBridgeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionFrameConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldLeafClosureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalGraphComposition
open InternalApplicationCertificateConstructors InternalApplicationCertifiedResultFoldClosure
open InternalApplicationCertifiedResultFoldLeafClosure InternalApplicationResultStackComposition
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationCertifiedResultFoldClosureBridgeProof
open InternalApplicationCertifiedResultFoldClosureBridgeStateProof
open InternalApplicationResultStackCompositionFrameConstructorsProof
open InternalApplicationResultStackCompositionBasicProof InternalApplicationResultStackCompositionStepProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel)
open InternalAcceptanceConjunctionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Coordinates are [original input, proposed leaf output]. Every auxiliary
value is supplied by internal Program graph totality, not a target premise. -/
def visitQ : Program 2 := pairOf (InternalAcceptance.constantZero 2) (.projection 0)
def workQ : Program 2 := consOf visitQ (InternalAcceptance.constantZero 2)
def singletonQ : Program 2 := consOf (.projection 1) (InternalAcceptance.constantZero 2)
def initialQ : Program 2 := .composition liveState ![workQ,InternalAcceptance.constantZero 2]
def terminalQ : Program 2 := .composition liveState ![InternalAcceptance.constantZero 2,singletonQ]
def payloadQ : Program 2 := .composition InternalUnpair.right (fun _ : Fin 1 => .projection 0)
def queries : Fin 6 → Program 2 := ![visitQ,workQ,singletonQ,initialQ,terminalQ,payloadQ]

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem leafFromQueries (guard leaf : Program 1) (combine : Program 4)
    (value out : OTerm α) (ys : Fin 6 → OTerm α)
    (hg : Nonempty (Derivation body Gamma
      (graph1 (InternalApplicationResultStack.openGuard guard) z value)))
    (hl : Nonempty (Derivation body Gamma (graph1 leaf out value)))
    (hq : ∀ i, Nonempty (Derivation body Gamma
      (programGraph (queries i) (ys i) (Fin.cons value (Fin.cons out Fin.elim0))))) :
    Nonempty (Derivation body Gamma (certifiedFold guard leaf combine out value)) := by
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
  have ht := leafTransitionAt guard leaf combine (ys 3) (ys 1) z (ys 0) value z
    (ys 4) out (ys 2) hi hw hv hg hl hc he
  have hr := runFrontBackward guard leaf combine (OrdinaryArithmetic.addTerm (ys 5) (ys 5))
    (ys 1) z (ys 2) (ys 3) z (ys 2) (ys 4) hi he ht
    (emptyRun guard leaf combine (OrdinaryArithmetic.addTerm (ys 5) (ys 5)) (ys 2))
  let unary : Fin 1 → OTerm α := Fin.cons value Fin.elim0
  have hvisit := binaryValue InternalPairing.pairing (InternalAcceptance.constantZero 1)
    (.projection 0) (ys 0) z value unary hv (constantZeroValue unary) (projectionValue 0 unary)
  have hwork : Nonempty (Derivation body Gamma (graph1 visitWork (ys 1) value)) :=
    binaryValue InternalListCodec.consCode (InternalApplicationResultStack.visitOf (.projection 0))
      (InternalAcceptance.constantZero 1) (ys 1) (ys 0) z unary hw hvisit (constantZeroValue unary)
  exact certifiedFoldOfRun guard leaf combine value (ys 5) (ys 1) out (ys 2) hp hwork hc hr

/-- Context-uniform continuation consuming only the two actual branch graphs. -/
theorem leafClosure (guard leaf : Program 1) (combine : Program 4)
    (value out : OTerm α)
    (hg : Nonempty (Derivation body Gamma
      (graph1 (InternalApplicationResultStack.openGuard guard) z value)))
    (hl : Nonempty (Derivation body Gamma (graph1 leaf out value))) :
    Nonempty (Derivation body Gamma (certifiedFold guard leaf combine out value)) := by
  apply queryCases queries (Fin.cons value (Fin.cons out Fin.elim0)) _
  intro β j ys Delta hj hq
  rw [certifiedFoldRename]
  have hg' := renameInto hg j Delta hj
  have hl' := renameInto hl j Delta hj
  simp only [graph1Rename,zRelabel] at hg' hl'
  simp only [consTermRename,emptyRename] at hq
  exact leafFromQueries guard leaf combine (value.relabel j) (out.relabel j) ys hg' hl' hq

theorem actualOriginalCertifiedResultFoldLeafClosure :
    InternalApplicationCertifiedResultFoldLeafClosureTargets.ActualOriginalCertifiedResultFoldLeafClosure := by
  intro body guard leaf combine α Gamma value out
  have h : Nonempty (Derivation body (leafGraphs guard leaf out value :: Gamma)
      (leafGraphs guard leaf out value)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨result⟩ := leafClosure guard leaf combine value out (andLeft h) (andRight h)
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldLeafClosureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldLeafClosureProof
