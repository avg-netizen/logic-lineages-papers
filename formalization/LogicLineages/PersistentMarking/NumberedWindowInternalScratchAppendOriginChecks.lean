module

public import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOriginTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOriginSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOriginChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue valueUnique)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalApplicationValidityStackAppendListProof (appendZeroValue consForward)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalListInduction (atCode atIndex constructorBody constructors)
open ID1Completion.InternalListInductionProof (actualOriginalListInductionAtCode)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (missGraph)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion headHit)
open NumberedWindowInternalSparseScratchMembership (scratchMember memberBase memberStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember tailMember)
open NumberedWindowInternalScratchAppendOpenTargets
open NumberedWindowInternalScratchAppendOpenSyntaxProof (appendRename testedRename appearsRename)
open NumberedWindowInternalScratchAppendOriginTargets
open NumberedWindowInternalScratchAppendOriginSyntaxProof

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem appendInputs (out raw suffix k : OTerm α)
    (h : Nonempty (Derivation body Γ (appendGraph out raw suffix))) (i : Fin 2) :
    Nonempty (Derivation body Γ
      (programGraph ((![appendCall,.projection 2] : Fin 2 → Program 3) i) (![out,k] i)
        ![raw,suffix,k])) := by
  let xs : Fin 3 → OTerm α := ![raw,suffix,k]
  have call : Nonempty (Derivation body Γ (programGraph appendCall out xs)) := by
    apply compositionValue append (![.projection 0,.projection 1] : Fin 2 → Program 3) out xs ![raw,suffix] h
    intro i
    exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs) (fun j => Fin.elim0 j)) i
  exact Fin.cases call (Fin.cases (projectionValue 2 xs) (fun j => Fin.elim0 j)) i

private theorem build (out raw suffix k : OTerm α)
    (h : Nonempty (Derivation body Γ (appendGraph out raw suffix)))
    (hit : Nonempty (Derivation body Γ (memberGraph out k))) :
    Nonempty (Derivation body Γ (tested raw suffix k)) :=
  compositionValue scratchMember ![appendCall,.projection 2] (suc z) ![raw,suffix,k] ![out,k]
    hit (appendInputs out raw suffix k h)

private theorem recover (out raw suffix k : OTerm α)
    (h : Nonempty (Derivation body Γ (appendGraph out raw suffix)))
    (hit : Nonempty (Derivation body Γ (tested raw suffix k))) :
    Nonempty (Derivation body Γ (memberGraph out k)) :=
  compositionRecover scratchMember ![appendCall,.projection 2] (suc z) ![raw,suffix,k] ![out,k]
    hit (appendInputs out raw suffix k h)

private theorem nilRule (suffix k : OTerm α) :
    Nonempty (Derivation body Γ (backAt z suffix k)) := by
  let H := tested z suffix k
  obtain ⟨actual⟩ := recover (body := body) (Γ := H :: Γ) suffix z suffix k
    (appendZeroValue suffix) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (orRight actual)⟩

private theorem carryTail (raw head tail suffix k : OTerm α)
    (cell : Derivation body Γ (consGraph raw head tail))
    (hit : Derivation body Γ (appears tail suffix k)) :
    Nonempty (Derivation body Γ (appears raw suffix k)) := by
  let A := memberGraph tail k
  let B := memberGraph suffix k
  obtain ⟨left⟩ := tailMember raw head tail k ⟨addHyp cell A⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination hit
    (Derivation.implicationIntroduction (orLeft left))
    (Derivation.implicationIntroduction (orRight (Derivation.hypothesis List.mem_cons_self)))⟩

private theorem wholeCons (out raw head tail suffix rest k : OTerm α)
    (cell : Derivation body Γ (consGraph raw head tail))
    (old : Derivation body Γ (backAt tail suffix k))
    (appendFull : Derivation body Γ (appendGraph out raw suffix))
    (appendTail : Derivation body Γ (appendGraph rest tail suffix))
    (member : Nonempty (Derivation body Γ (memberGraph out k))) :
    Nonempty (Derivation body Γ (appears raw suffix k)) := by
  have next := consForward raw head tail suffix rest out ⟨cell⟩ ⟨appendTail⟩ ⟨appendFull⟩
  obtain ⟨whereIt⟩ := consInversion out head rest k next member
  let H := (missGraph head k).not
  let T := memberGraph rest k
  obtain ⟨headIn⟩ := headHit raw head tail k ⟨addHyp cell H⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨seen⟩ := build (body := body) (Γ := T :: Γ) rest tail suffix k
    ⟨addHyp appendTail T⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨tailIn⟩ := carryTail raw head tail suffix k (addHyp cell T)
    (Derivation.implicationElimination (addHyp old T) seen)
  exact ⟨disjunctionElimination whereIt
    (Derivation.implicationIntroduction (orLeft headIn))
    (Derivation.implicationIntroduction tailIn)⟩

private theorem atOutput (out raw head tail suffix k : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph raw head tail)))
    (old : Nonempty (Derivation body Γ (backAt tail suffix k)))
    (appended : Nonempty (Derivation body Γ (appendGraph out raw suffix)))
    (test : Nonempty (Derivation body Γ (tested raw suffix k))) :
    Nonempty (Derivation body Γ (appears raw suffix k)) := by
  apply programCases append ![tail,suffix] _
  intro β j Δ rest keep tailRun
  rw [appearsRename]
  simp only [binaryInputsRename] at tailRun
  have c := renameInto cell j Δ keep
  have h := renameInto old j Δ keep
  have f := renameInto appended j Δ keep
  have t := renameInto test j Δ keep
  rw [consGraphRename] at c
  rw [backAtRename] at h
  rw [appendRename] at f
  rw [testedRename] at t
  obtain ⟨c⟩ := c
  obtain ⟨h⟩ := h
  obtain ⟨fc⟩ := f
  obtain ⟨tailRun⟩ := tailRun
  exact wholeCons (out.relabel j) (raw.relabel j) (head.relabel j) (tail.relabel j)
    (suffix.relabel j) rest (k.relabel j) c h fc tailRun
    (recover (out.relabel j) (raw.relabel j) (suffix.relabel j) (k.relabel j) ⟨fc⟩ t)

private theorem onCons (raw head tail suffix k : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph raw head tail)))
    (old : Nonempty (Derivation body Γ (backAt tail suffix k))) :
    Nonempty (Derivation body Γ (backAt raw suffix k)) := by
  let H := tested raw suffix k
  let Δ := H :: Γ
  have present : Nonempty (Derivation body Δ H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨cell⟩ := cell
  obtain ⟨old⟩ := old
  have outMember : Nonempty (Derivation body Δ (appears raw suffix k)) := by
    apply programCases append ![raw,suffix] _
    intro β j Θ out keep full
    rw [appearsRename]
    simp only [binaryInputsRename] at full
    have c := renameInto (show Nonempty (Derivation body Δ (consGraph raw head tail)) from
      ⟨addHyp cell H⟩) j Θ keep
    have h := renameInto (show Nonempty (Derivation body Δ (backAt tail suffix k)) from
      ⟨addHyp old H⟩) j Θ keep
    have t := renameInto present j Θ keep
    rw [consGraphRename] at c
    rw [backAtRename] at h
    simp only [H,testedRename] at t
    exact atOutput out (raw.relabel j) (head.relabel j) (tail.relabel j) (suffix.relabel j)
      (k.relabel j) c h full t
  obtain ⟨outMember⟩ := outMember
  exact ⟨Derivation.implicationIntroduction outMember⟩

private theorem allCons (suffix k : OTerm α) :
    Nonempty (Derivation body Γ (constructors (backMotive suffix k))) := by
  apply actualFiniteUniversalIntroduction body α 3 Γ (constructorBody (backMotive suffix k))
  let j : α → α ⊕ Fin 3 := Sum.inl
  let raw : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let head : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let tail : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let H := consGraph raw head tail
  let Old := backAt tail (suffix.relabel j) (k.relabel j)
  let Δ := Old :: H :: Γ.map (fun h => h.relabel j)
  change Nonempty (Derivation body (Γ.map (fun h => h.relabel j))
    (H.imp ((atIndex (backMotive suffix k) 2).imp (atIndex (backMotive suffix k) 0))))
  simp only [atIndexEq]
  obtain ⟨out⟩ := onCons (body := body) (Γ := Δ) raw head tail (suffix.relabel j) (k.relabel j)
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction out)⟩

theorem exact_OpenScratchAppendOrigin : ExactOpenScratchAppendOrigin := by
  intro body α Γ raw suffix out k appended hit
  have nil : Nonempty (Derivation body Γ (atCode (backMotive suffix k) z)) := by
    rw [atCodeEq]
    exact nilRule suffix k
  obtain ⟨base⟩ := nil
  obtain ⟨step⟩ := allCons (body := body) (Γ := Γ) suffix k
  have d := actualOriginalListInductionAtCode body α Γ (backMotive suffix k) raw
    ⟨Derivation.conjunctionIntroduction base step⟩
  rw [atCodeEq] at d
  obtain ⟨d⟩ := d
  obtain ⟨actual⟩ := build out raw suffix k appended hit
  exact ⟨Derivation.implicationElimination d actual⟩

#print axioms exact_OpenScratchAppendOrigin

end LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOriginChecks
