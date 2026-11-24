module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchConsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchConsFailureProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchConsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename inputsRename)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalDirectBoundaryGuardsTargets (normalizeScalar typedScratch)
open NumberedWindowInternalDirectTypedScratchReportTargets (normalizedMap Reports)
open NumberedWindowInternalDirectTypedScratchReportProof (exact_EliminateTypedScratch exact_IntroduceTypedScratch)
open NumberedWindowInternalDirectTypedScratchConsFailureProof (tailMiss scalarAtMappedHead)
open NumberedWindowInternalDirectTypedScratchConsTargets

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem carryMap {β : Type} (i : Program 1) (q m : OTerm α) (ρ : α → β)
    (Δ : List (Formula β)) (keep : ∀ p ∈ Γ, p.relabel ρ ∈ Δ) (h : Reports i B Γ q m) :
    Reports i B Δ (q.relabel ρ) (m.relabel ρ) := by
  constructor
  · simpa only [unaryRename] using renameInto h.mappedCall ρ Δ keep
  · simpa only [programRename,binaryInputsRename,zRelabel] using renameInto h.missingZero ρ Δ keep

private theorem completeCons (i : Program 1) (code head tail mapped mh mt : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph code head tail)))
    (h : Reports i B Γ code mapped)
    (headRun : Nonempty (Derivation B Γ (unary (normalizeScalar i) mh head)))
    (tailRun : Nonempty (Derivation B Γ (unary (normalizedMap i) mt tail))) :
    Nonempty (Derivation B Γ (unary i (suc z) head ⊓ unary (typedScratch i) (suc z) tail)) := by
  have mc : Nonempty (Derivation B Γ (consGraph mapped mh mt)) :=
    ID1Completion.InternalListMapProof.consForward (k := 0) (normalizeScalar i) code head tail
      mh mt mapped Fin.elim0 cell headRun tailRun h.mappedCall
  obtain ⟨headBit⟩ := scalarAtMappedHead i head mapped mh mt headRun mc h.missingZero
  obtain ⟨tailBit⟩ := exact_IntroduceTypedScratch i B α Γ tail mt
    ⟨tailRun,tailMiss mapped mh mt mc h.missingZero⟩
  exact ⟨Derivation.conjunctionIntroduction headBit tailBit⟩

private theorem mapCons (i : Program 1) (code head tail mapped : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph code head tail)))
    (h : Reports i B Γ code mapped) :
    Nonempty (Derivation B Γ (unary i (suc z) head ⊓ unary (typedScratch i) (suc z) tail)) := by
  apply programCases (normalizeScalar i) ![head] _
  intro β j Δ mh keep hcall
  simp only [conjunctionRename,unaryRename,sucRelabel,zRelabel]
  have h1 := carryMap i code mapped j Δ keep h
  have c1 : Nonempty (Derivation B Δ (consGraph (code.relabel j) (head.relabel j) (tail.relabel j))) := by
    simpa only [consGraphRename] using renameInto cell j Δ keep
  have hcall1 : Nonempty (Derivation B Δ (unary (normalizeScalar i) mh (head.relabel j))) := by
    simpa only [unary,inputsRename] using hcall
  apply programCases (normalizedMap i) ![tail.relabel j] _
  intro γ k Ω mt retain tcall
  simp only [conjunctionRename,unaryRename,sucRelabel,zRelabel]
  let C := (code.relabel j).relabel k
  let H := (head.relabel j).relabel k
  let T := (tail.relabel j).relabel k
  have saved : Nonempty (Derivation B Ω (consGraph C H T)) := by
    simpa only [C,H,T,consGraphRename] using renameInto c1 k Ω retain
  have actualHead : Nonempty (Derivation B Ω (unary (normalizeScalar i) (mh.relabel k) H)) := by
    simpa only [H,unaryRename] using renameInto hcall1 k Ω retain
  have actualTail : Nonempty (Derivation B Ω (unary (normalizedMap i) mt T)) := by
    simpa only [T,unary,inputsRename] using tcall
  exact completeCons i C H T ((mapped.relabel j).relabel k) (mh.relabel k) mt saved
    (carryMap i (code.relabel j) (mapped.relabel j) k Ω retain h1) actualHead actualTail

theorem exact_TypedScratchCons : ExactTypedScratchCons := by
  intro i B α Γ code head tail cell held
  apply exact_EliminateTypedScratch i B α Γ code
    (unary i (suc z) head ⊓ unary (typedScratch i) (suc z) tail) held
  intro β ρ Δ mapped keep h
  simp only [conjunctionRename,unaryRename,sucRelabel,zRelabel]
  have actualCell : Nonempty (Derivation B Δ (consGraph (code.relabel ρ) (head.relabel ρ) (tail.relabel ρ))) := by
    simpa only [consGraphRename] using renameInto cell ρ Δ keep
  exact mapCons i (code.relabel ρ) (head.relabel ρ) (tail.relabel ρ) mapped actualCell h

#print axioms exact_TypedScratchCons
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchConsProof
