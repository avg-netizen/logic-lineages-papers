module

public import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowSingletonProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenChecks
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
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion)
open NumberedWindowInternalSparseRoundWindowSingletonProof (nonzeroEquality)
open NumberedWindowInternalSparseScratchMembership (scratchMember memberBase memberStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember tailMember)
open NumberedWindowInternalScratchAppendOpenTargets
open NumberedWindowInternalScratchAppendOpenSyntaxProof

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
    Nonempty (Derivation body Γ (atList z suffix k)) := by
  let A := memberGraph z k
  let B := memberGraph suffix k
  let Δ := (A ⊔ B) :: Γ
  have current : Derivation body Δ (A ⊔ B) := Derivation.hypothesis List.mem_cons_self
  have bad := nilRecover (body := body) (Gamma := A :: Δ) memberBase memberStep
    (suc z) (![k] : Fin 1 → OTerm α) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨no⟩ := valueUnique memberBase (suc z) z ![k] bad (zeroConstantValue _)
  obtain ⟨yes⟩ := build (body := body) (Γ := B :: Δ) suffix z suffix k
    (appendZeroValue suffix) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (disjunctionElimination current
    (Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply no)))
    (Derivation.implicationIntroduction yes))⟩

private theorem tailOutcome (out head tail suffix rest k : OTerm α)
    (induction : Derivation body Γ (atList tail suffix k))
    (succCell : Derivation body Γ (consGraph out head rest))
    (tailRun : Derivation body Γ (appendGraph rest tail suffix))
    (side : Derivation body Γ (appears tail suffix k)) :
    Nonempty (Derivation body Γ (memberGraph out k)) := by
  have tailHit := recover rest tail suffix k ⟨tailRun⟩
    ⟨Derivation.implicationElimination induction side⟩
  exact tailMember out head rest k ⟨succCell⟩ tailHit

private theorem wholeCons (out raw head tail suffix rest k : OTerm α)
    (cell : Derivation body Γ (consGraph raw head tail))
    (old : Derivation body Γ (atList tail suffix k))
    (appendFull : Derivation body Γ (appendGraph out raw suffix))
    (appendTail : Derivation body Γ (appendGraph rest tail suffix))
    (side : Derivation body Γ (appears raw suffix k)) :
    Nonempty (Derivation body Γ (memberGraph out k)) := by
  obtain ⟨next⟩ := consForward raw head tail suffix rest out ⟨cell⟩ ⟨appendTail⟩ ⟨appendFull⟩
  let A := memberGraph raw k
  let B := memberGraph suffix k
  let H := (missGraph head k).not
  let L := memberGraph tail k
  obtain ⟨fromLeft⟩ : Nonempty (Derivation body (A :: Γ) (memberGraph out k)) := by
    obtain ⟨whereLeft⟩ := consInversion raw head tail k ⟨addHyp cell A⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := nonzeroEquality (body := body) (Γ := H :: A :: Γ) head k
      (Derivation.hypothesis List.mem_cons_self)
    obtain ⟨hitHead⟩ := headMember out head rest k ⟨addHyp (addHyp next A) H⟩ ⟨symm he⟩
    obtain ⟨hitTail⟩ := tailOutcome out head tail suffix rest k (addHyp (addHyp old A) L)
      (addHyp (addHyp next A) L) (addHyp (addHyp appendTail A) L)
      (orLeft (Derivation.hypothesis List.mem_cons_self))
    exact ⟨disjunctionElimination whereLeft (Derivation.implicationIntroduction hitHead)
      (Derivation.implicationIntroduction hitTail)⟩
  obtain ⟨fromRight⟩ := tailOutcome out head tail suffix rest k (addHyp old B) (addHyp next B)
    (addHyp appendTail B) (orRight (Derivation.hypothesis List.mem_cons_self))
  exact ⟨disjunctionElimination side (Derivation.implicationIntroduction fromLeft)
    (Derivation.implicationIntroduction fromRight)⟩

private theorem onCons (raw head tail suffix k : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph raw head tail)))
    (old : Nonempty (Derivation body Γ (atList tail suffix k))) :
    Nonempty (Derivation body Γ (atList raw suffix k)) := by
  let A := appears raw suffix k
  let Δ := A :: Γ
  have hit : Nonempty (Derivation body Δ A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨cell⟩ := cell
  obtain ⟨old⟩ := old
  have t : Nonempty (Derivation body Δ (tested raw suffix k)) := by
    apply programCases append ![raw,suffix] _
    intro β j Θ out keep full
    rw [testedRename]
    simp only [binaryInputsRename] at full
    have c := renameInto (show Nonempty (Derivation body Δ (consGraph raw head tail)) from
      ⟨addHyp cell A⟩) j Θ keep
    have h := renameInto (show Nonempty (Derivation body Δ (atList tail suffix k)) from
      ⟨addHyp old A⟩) j Θ keep
    have selected := renameInto hit j Θ keep
    simp only [consGraphRename] at c
    simp only [atListRename] at h
    simp only [A,appearsRename] at selected
    let raw' := raw.relabel j
    let head' := head.relabel j
    let tail' := tail.relabel j
    let suffix' := suffix.relabel j
    let k' := k.relabel j
    apply build out raw' suffix' k' full
    apply programCases append ![tail',suffix'] _
    intro γ j' Φ rest keep' next
    rw [graphRename]
    simp only [binaryInputsRename] at next
    have c' := renameInto c j' Φ keep'
    have h' := renameInto h j' Φ keep'
    have f' := renameInto (show Nonempty (Derivation body Θ (appendGraph out raw' suffix')) from full) j' Φ keep'
    have s' := renameInto selected j' Φ keep'
    simp only [consGraphRename] at c'
    simp only [atListRename] at h'
    simp only [appendRename] at f'
    simp only [appearsRename] at s'
    obtain ⟨c'⟩ := c'
    obtain ⟨h'⟩ := h'
    obtain ⟨f'⟩ := f'
    obtain ⟨next⟩ := next
    obtain ⟨s'⟩ := s'
    exact wholeCons (out.relabel j') (raw'.relabel j') (head'.relabel j') (tail'.relabel j')
      (suffix'.relabel j') rest (k'.relabel j') c' h' f' next s'
  obtain ⟨t⟩ := t
  exact ⟨Derivation.implicationIntroduction t⟩

private theorem allCons (suffix k : OTerm α) :
    Nonempty (Derivation body Γ (constructors (motive suffix k))) := by
  apply actualFiniteUniversalIntroduction body α 3 Γ (constructorBody (motive suffix k))
  let j : α → α ⊕ Fin 3 := Sum.inl
  let raw : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let head : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let tail : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let H := consGraph raw head tail
  let Old := atList tail (suffix.relabel j) (k.relabel j)
  let Δ := Old :: H :: Γ.map (fun h => h.relabel j)
  change Nonempty (Derivation body (Γ.map (fun h => h.relabel j))
    (H.imp ((atIndex (motive suffix k) 2).imp (atIndex (motive suffix k) 0))))
  simp only [atIndexEq]
  obtain ⟨out⟩ := onCons (body := body) (Γ := Δ) raw head tail (suffix.relabel j) (k.relabel j)
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction out)⟩

theorem exact_OpenScratchAppendMembership : ExactOpenScratchAppendMembership := by
  intro body α Γ raw suffix out k appended occurs
  have base : Nonempty (Derivation body Γ (atCode (motive suffix k) z)) := by
    rw [atCodeEq]
    exact nilRule suffix k
  obtain ⟨base⟩ := base
  obtain ⟨step⟩ := allCons (body := body) (Γ := Γ) suffix k
  have d := actualOriginalListInductionAtCode body α Γ (motive suffix k) raw
    ⟨Derivation.conjunctionIntroduction base step⟩
  rw [atCodeEq] at d
  obtain ⟨d⟩ := d
  obtain ⟨occurs⟩ := occurs
  exact recover out raw suffix k appended ⟨Derivation.implicationElimination d occurs⟩

theorem fromLeft (raw suffix out k : OTerm α)
    (appended : Nonempty (Derivation body Γ (appendGraph out raw suffix)))
    (occurs : Nonempty (Derivation body Γ (memberGraph raw k))) :
    Nonempty (Derivation body Γ (memberGraph out k)) := by
  obtain ⟨occurs⟩ := occurs
  exact exact_OpenScratchAppendMembership body α Γ raw suffix out k appended ⟨orLeft occurs⟩

theorem fromRight (raw suffix out k : OTerm α)
    (appended : Nonempty (Derivation body Γ (appendGraph out raw suffix)))
    (occurs : Nonempty (Derivation body Γ (memberGraph suffix k))) :
    Nonempty (Derivation body Γ (memberGraph out k)) := by
  obtain ⟨occurs⟩ := occurs
  exact exact_OpenScratchAppendMembership body α Γ raw suffix out k appended ⟨orRight occurs⟩

#print axioms exact_OpenScratchAppendMembership

end LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenChecks
