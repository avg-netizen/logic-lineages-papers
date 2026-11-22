module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldImageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOriginChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalControlGraphSupportProof (valueUnique projectionValue)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalListInduction (atCode atIndex constructorBody constructors)
open ID1Completion.InternalListInductionProof (actualOriginalListInductionAtCode)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (consTermRename)
open ID1Completion.InternalRawListRecursionProof (nilRecover consForward stepCases)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalListMap (mapHead)
open ID1Completion.InternalListMapProof (mapHeadValue)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open NumberedWindowInternalSparseScratchMembership (memberBase memberStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverCartesianFoldTargets
open NumberedWindowInternalCoverCartesianFoldSyntaxProof (flatRename imageRename)
open NumberedWindowInternalCoverCartesianFoldImageProof (imageOfMember memberOfImage)
open NumberedWindowInternalScratchAppendOriginChecks (exact_OpenScratchAppendOrigin)
open NumberedWindowInternalCoverCartesianFoldOriginTargets
open NumberedWindowInternalCoverCartesianFoldOriginSyntaxProof
open NumberedWindowInternalCoverCartesianFoldOriginWitnessProof (atHead fromTail hitOfBlockMember)

attribute [local irreducible] programGraph
variable {k : Nat} {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem nilRule (D : Program (k+1)) (image : OTerm α) (params : Fin k → OTerm α) :
    Nonempty (Derivation body Γ (originAt D z image params)) := by
  let H := imageGraph D z image params
  have nilRun : Nonempty (Derivation body (H :: Γ) (flatGraph D z z params)) :=
    ID1Completion.InternalRawListRecursionProof.nilValue (constantZero k) (flatStep D) z params
      (zeroConstantValue params)
  have nilHit := memberOfImage D z z image params nilRun
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have nilValue := nilRecover memberBase memberStep (suc z) (![image] : Fin 1 → OTerm α) nilHit
  obtain ⟨falseEq⟩ := valueUnique memberBase (suc z) z (![image] : Fin 1 → OTerm α)
    nilValue (zeroConstantValue _)
  exact ⟨Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply falseEq))⟩

private theorem fromAppend (D : Program (k+1)) (raw head tail image out block rest : OTerm α)
    (params : Fin k → OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph raw head tail)))
    (hit : Nonempty (Derivation body Γ (memberGraph out image)))
    (headRun : Nonempty (Derivation body Γ (programGraph D block (Fin.cons head params))))
    (tailRun : Nonempty (Derivation body Γ (flatGraph D rest tail params)))
    (appended : Nonempty (Derivation body Γ (programGraph append out ![block,rest])))
    (ih : Nonempty (Derivation body Γ (originAt D tail image params))) :
    Nonempty (Derivation body Γ (hasOrigin D raw image params)) := by
  obtain ⟨whereIt⟩ := exact_OpenScratchAppendOrigin body α Γ block rest out image appended hit
  let A := memberGraph block image
  let B := memberGraph rest image
  have left : Nonempty (Derivation body (A :: Γ) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨first⟩ := atHead D raw head tail image params (withHyp cell A)
    (hitOfBlockMember D head image block params (withHyp headRun A) left)
  have right : Nonempty (Derivation body (B :: Γ) B) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨tailImage⟩ := imageOfMember D rest tail image params (withHyp tailRun B) right
  obtain ⟨useIH⟩ := withHyp ih B
  obtain ⟨second⟩ := fromTail D raw head tail image params (withHyp cell B)
    ⟨Derivation.implicationElimination useIH tailImage⟩
  exact ⟨disjunctionElimination whereIt (Derivation.implicationIntroduction first)
    (Derivation.implicationIntroduction second)⟩

private theorem fromStep (D : Program (k+1)) (raw head tail image out rest : OTerm α)
    (params : Fin k → OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph raw head tail)))
    (hit : Nonempty (Derivation body Γ (memberGraph out image)))
    (step : Nonempty (Derivation body Γ (programGraph (flatStep D) out (Fin.cons head (Fin.cons rest params)))))
    (tailRun : Nonempty (Derivation body Γ (flatGraph D rest tail params)))
    (ih : Nonempty (Derivation body Γ (originAt D tail image params))) :
    Nonempty (Derivation body Γ (hasOrigin D raw image params)) := by
  apply programCases D (Fin.cons head params) _
  intro β j Δ block keep headRun
  rw [originRename]
  simp only [consTermRename] at headRun
  have cell' := renameInto cell j Δ keep
  have hit' := renameInto hit j Δ keep
  have step' := renameInto step j Δ keep
  have tail' := renameInto tailRun j Δ keep
  have ih' := renameInto ih j Δ keep
  rw [consGraphRename] at cell'
  rw [graphRename] at hit'
  simp only [ID1Completion.InternalControlGraphSupportProof.programRename,consTermRename] at step'
  rw [flatRename] at tail'
  rw [originAtRename] at ih'
  let ps : Fin k → OTerm β := fun i => (params i).relabel j
  let xs : Fin (k+2) → OTerm β := Fin.cons (head.relabel j) (Fin.cons (rest.relabel j) ps)
  have left := mapHeadValue D (head.relabel j) (rest.relabel j) block ps headRun
  have extract : Nonempty (Derivation body Δ (programGraph append (out.relabel j) ![block,rest.relabel j])) := by
    apply compositionRecover append ![mapHead D,.projection 1] (out.relabel j) xs ![block,rest.relabel j] step'
    intro i
    exact Fin.cases left (Fin.cases (projectionValue 1 xs) (fun n => Fin.elim0 n)) i
  exact fromAppend D (raw.relabel j) (head.relabel j) (tail.relabel j)
    (image.relabel j) (out.relabel j) block (rest.relabel j) ps cell' hit' headRun tail' extract ih'

private theorem onCons (D : Program (k+1)) (raw head tail image out : OTerm α) (params : Fin k → OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph raw head tail)))
    (hit : Nonempty (Derivation body Γ (memberGraph out image)))
    (run : Nonempty (Derivation body Γ (flatGraph D out raw params)))
    (ih : Nonempty (Derivation body Γ (originAt D tail image params))) :
    Nonempty (Derivation body Γ (hasOrigin D raw image params)) := by
  have step := consForward (constantZero k) (flatStep D) raw head tail out params cell run
  apply stepCases (constantZero k) (flatStep D) out head tail params _ step
  intro β j Δ rest keep tailRun rowRun
  rw [originRename]
  have cell' := renameInto cell j Δ keep
  have hit' := renameInto hit j Δ keep
  have ih' := renameInto ih j Δ keep
  rw [consGraphRename] at cell'
  rw [graphRename] at hit'
  rw [originAtRename] at ih'
  exact fromStep D (raw.relabel j) (head.relabel j) (tail.relabel j) (image.relabel j)
    (out.relabel j) rest (fun i => (params i).relabel j) cell' hit' rowRun tailRun ih'

private theorem consRule (D : Program (k+1)) (raw head tail image : OTerm α) (params : Fin k → OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph raw head tail)))
    (ih : Nonempty (Derivation body Γ (originAt D tail image params))) :
    Nonempty (Derivation body Γ (originAt D raw image params)) := by
  let H := imageGraph D raw image params
  have given : Nonempty (Derivation body (H :: Γ) H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have found : Nonempty (Derivation body (H :: Γ) (hasOrigin D raw image params)) := by
    apply programCases (flatMap D) (Fin.cons raw params) _
    intro β j Δ out keep run
    rw [originRename]
    simp only [consTermRename] at run
    have cell' := renameInto (withHyp cell H) j Δ keep
    have ih' := renameInto (withHyp ih H) j Δ keep
    have image' := renameInto given j Δ keep
    rw [consGraphRename] at cell'
    rw [originAtRename] at ih'
    simp only [H,imageRename] at image'
    let p : Fin k → OTerm β := fun i => (params i).relabel j
    exact onCons D (raw.relabel j) (head.relabel j) (tail.relabel j) (image.relabel j)
      out p cell' (memberOfImage D out (raw.relabel j) (image.relabel j) p run image') run ih'
  obtain ⟨found⟩ := found
  exact ⟨Derivation.implicationIntroduction found⟩

private theorem allCons (D : Program (k+1)) (image : OTerm α) (params : Fin k → OTerm α) :
    Nonempty (Derivation body Γ (constructors (motive D image params))) := by
  apply actualFiniteUniversalIntroduction body α 3 Γ (constructorBody (motive D image params))
  let j : α → α ⊕ Fin 3 := Sum.inl
  let raw : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let head : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let tail : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let p : Fin k → OTerm (α ⊕ Fin 3) := fun i => (params i).relabel j
  let H := consGraph raw head tail
  let Old := originAt D tail (image.relabel j) p
  let Δ := Old :: H :: Γ.map (fun h => h.relabel j)
  change Nonempty (Derivation body (Γ.map (fun h => h.relabel j))
    (H.imp ((atIndex (motive D image params) 2).imp (atIndex (motive D image params) 0))))
  simp only [atIndexEq]
  obtain ⟨d⟩ := consRule (body := body) (Γ := Δ) D raw head tail (image.relabel j) p
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩

theorem exact_OpenCartesianFoldOrigin : ExactOpenCartesianFoldOrigin := by
  intro k D body α Γ raw image out params run hit
  have nil : Nonempty (Derivation body Γ (atCode (motive D image params) z)) := by
    rw [atCodeEq]
    exact nilRule D image params
  obtain ⟨base⟩ := nil
  obtain ⟨step⟩ := allCons (body := body) (Γ := Γ) D image params
  have law := actualOriginalListInductionAtCode body α Γ (motive D image params) raw
    ⟨Derivation.conjunctionIntroduction base step⟩
  rw [atCodeEq] at law
  obtain ⟨law⟩ := law
  obtain ⟨actual⟩ := imageOfMember D out raw image params run hit
  exact ⟨Derivation.implicationElimination law actual⟩

#print axioms exact_OpenCartesianFoldOrigin

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginChecks
