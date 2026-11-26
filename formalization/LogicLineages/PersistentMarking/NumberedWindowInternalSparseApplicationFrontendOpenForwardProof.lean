module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenChooseProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenForwardProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalControlGraphSupportProof (outputTransport)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeParsedEmitter
  (addressGood arrowGood rawContext rawResult rawLeast rawDomain rawCodomain)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressReports arrowReports)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph3Rename)
open NumberedWindowInternalSparseAddressPositiveOpenTapeProof (slotRead)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore applicationGuard)
open NumberedWindowInternalSparseApplicationFrontendTargets (applicationReport)
open NumberedWindowInternalSparseApplicationFrontendOpenGateProof (G args readCore readGuard)
open NumberedWindowInternalSparseApplicationFrontendOpenCallProof (readCompare readOutput)
open NumberedWindowInternalSparseApplicationFrontendOpenChooseProof (Observed choose)
open NumberedWindowInternalSparseApplicationFrontendOpenBindingProof (row someRow someRowRename supply)
open NumberedWindowInternalSparseApplicationFrontendOpenShapeProof (assembleInputs)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem fields (x c t l : OTerm α)
    (ctx : Nonempty (Derivation body Γ (unary rawContext c x)))
    (ty : Nonempty (Derivation body Γ (unary rawResult t x)))
    (cls : Nonempty (Derivation body Γ (unary rawLeast l x))) :
    Nonempty (Derivation body Γ (addressReports x c t l)) := by
  obtain ⟨a⟩ := ctx
  obtain ⟨b⟩ := ty
  obtain ⟨e⟩ := cls
  exact ⟨Derivation.conjunctionIntroduction a (Derivation.conjunctionIntroduction b e)⟩

private theorem afterFields (least : Program 3) (f u y : OTerm α) (ys : Fin 8 → OTerm α)
    (accepted : G body Γ (applicationCore least) (args f u y))
    (seen : Observed body Γ (args f u y) ys) :
    Nonempty (Derivation body Γ (someRow least f u y)) := by
  let xs := args f u y
  let c := ys 0
  let r := ys 1
  let d := ys 2
  let e := ys 3
  let fn := ys 4
  let arg := ys 7
  have p := readCore least xs accepted
  obtain ⟨sameC⟩ := readCompare rawContext rawContext xs c (ys 5) (seen 0) (seen 5) p.ctxEq
  obtain ⟨sameD⟩ := readCompare rawDomain rawResult xs d (ys 6) (seen 2) (seen 6) p.domEq
  have left := fields f c r fn (slotRead rawContext 0 c xs (seen 0))
    (slotRead rawResult 0 r xs (seen 1)) (slotRead rawLeast 0 fn xs (seen 4))
  have rc := outputTransport rawContext (ys 5) c (![u] : Fin 1 → OTerm α) ⟨symm sameC⟩
    (slotRead rawContext 1 (ys 5) xs (seen 5))
  have rd := outputTransport rawResult (ys 6) d (![u] : Fin 1 → OTerm α) ⟨symm sameD⟩
    (slotRead rawResult 1 (ys 6) xs (seen 6))
  have right := fields u c d arg rc rd (slotRead rawLeast 1 arg xs (seen 7))
  obtain ⟨hd⟩ := slotRead rawDomain 0 d xs (seen 2)
  obtain ⟨he⟩ := slotRead rawCodomain 0 e xs (seen 3)
  have arrow : Nonempty (Derivation body Γ (arrowReports f d e)) :=
    ⟨Derivation.conjunctionIntroduction hd he⟩
  obtain ⟨inputs⟩ := assembleInputs f u c r d e fn arg
    (slotRead addressGood 0 (suc z) xs p.fShape) (slotRead addressGood 1 (suc z) xs p.uShape)
    (slotRead arrowGood 0 (suc z) xs p.fArrow) left right arrow
  obtain ⟨output⟩ := readOutput least xs c d e fn arg (seen 0) (seen 2) (seen 3) (seen 4)
    (seen 7) p.output
  exact supply least f u y c r d e fn arg ⟨Derivation.conjunctionIntroduction inputs output⟩

private theorem coreForward (least : Program 3) (f u y : OTerm α)
    (accepted : G body Γ (applicationCore least) (args f u y)) :
    Nonempty (Derivation body Γ (someRow least f u y)) := by
  apply choose f u y (someRow least f u y)
  intro β j Δ ys hJ observed
  rw [someRowRename]
  have known := renameInto accepted j Δ hJ
  change Nonempty (Derivation body Δ ((programGraph (applicationCore least) (suc z) ![f,u,y]).relabel j)) at known
  rw [graph3Rename,sucRelabel,zRelabel] at known
  exact afterFields least (f.relabel j) (u.relabel j) (y.relabel j) ys known observed

theorem forward (i : Program 1) (least : Program 3) (f u y : OTerm α)
    (accepted : G body Γ (applicationGuard i least) (args f u y)) :
    Nonempty (Derivation body Γ (applicationReport i least f u y)) := by
  obtain ⟨⟨left⟩,⟨right⟩,core⟩ := readGuard i least f u y accepted
  obtain ⟨data⟩ := coreForward least f u y core
  exact ⟨Derivation.conjunctionIntroduction left (Derivation.conjunctionIntroduction right data)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenForwardProof
