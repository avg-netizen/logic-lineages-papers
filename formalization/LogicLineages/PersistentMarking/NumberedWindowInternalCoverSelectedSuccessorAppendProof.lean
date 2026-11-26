module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorAtomProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAppendInclusionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTransportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorAppendProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCompositionCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalScratchAppendOpenSyntaxProof (appendRename)
open NumberedWindowInternalCoverArgumentCellsTargets (axisInclusion)
open NumberedWindowInternalCoverArgumentCellsTransportProof (axisRename)
open NumberedWindowInternalCoverAppendInclusionProof (exact_OpenOriginalAppendInclusion)
open NumberedWindowInternalCoverSelectedSuccessorTargets
open NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof
open NumberedWindowInternalCoverSelectedSuccessorAtomProof

attribute [local irreducible] programGraph

private theorem appendTape {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (out : OTerm α) (ys : Fin 2 → OTerm α)
    (actual : Nonempty (Derivation body Γ (programGraph append out ys))) :
    Nonempty (Derivation body Γ (appendGraph out (ys 0) (ys 1))) := by
  have same : ys = ![ys 0,ys 1] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  rw [same] at actual
  exact actual

theorem includeJoin (P Q : Program 5) (ip : OpenPartInclusion P) (iq : OpenPartInclusion Q) :
    OpenPartInclusion (join P Q) := by
  intro body α Γ old next H K ids ids' ts ts' args args' small large hi ht ha
  let sels : Fin 2 → Program 5 := Fin.cons P (Fin.cons Q Fin.elim0)
  let oldTape := stepTape H K ids ts args
  apply programCompositionCases append sels old oldTape (axisInclusion old next) small
  intro β j oldVals Δ keep oldAppend inputsOld
  rw [axisRename]
  let H₁ := H.relabel j
  let K₁ := K.relabel j
  let i₁ := ids.relabel j
  let i'₁ := ids'.relabel j
  let t₁ := ts.relabel j
  let t'₁ := ts'.relabel j
  let a₁ := args.relabel j
  let a'₁ := args'.relabel j
  let o₁ := old.relabel j
  let n₁ := next.relabel j
  have before := appendTape o₁ oldVals oldAppend
  have ap := inputsOld 0
  have aq := inputsOld 1
  change Nonempty (Derivation body Δ (programGraph P (oldVals 0)
    (fun i => (stepTape H K ids ts args i).relabel j))) at ap
  change Nonempty (Derivation body Δ (programGraph Q (oldVals 1)
    (fun i => (stepTape H K ids ts args i).relabel j))) at aq
  rw [tapeRename] at ap aq
  have large₁ := renameInto large j Δ keep
  have hi₁ := renameInto hi j Δ keep
  have ht₁ := renameInto ht j Δ keep
  have ha₁ := renameInto ha j Δ keep
  rw [reportRename] at large₁
  rw [axisRename] at hi₁ ht₁ ha₁
  apply programCompositionCases append sels n₁ (stepTape H₁ K₁ i'₁ t'₁ a'₁)
    (axisInclusion o₁ n₁) large₁
  intro γ k newVals Θ preserve newAppend inputsNew
  rw [axisRename]
  have after := appendTape (n₁.relabel k) newVals newAppend
  have before' := renameInto before k Θ preserve
  rw [appendRename] at before'
  have p₁ : Nonempty (Derivation body Δ (stepReport P (oldVals 0) H₁ K₁ i₁ t₁ a₁)) := ap
  have q₁ : Nonempty (Derivation body Δ (stepReport Q (oldVals 1) H₁ K₁ i₁ t₁ a₁)) := aq
  have p₁' := renameInto p₁ k Θ preserve
  have q₁' := renameInto q₁ k Θ preserve
  rw [reportRename] at p₁' q₁'
  have p₂ := inputsNew 0
  have q₂ := inputsNew 1
  change Nonempty (Derivation body Θ (programGraph P (newVals 0)
    (fun i => (stepTape H₁ K₁ i'₁ t'₁ a'₁ i).relabel k))) at p₂
  change Nonempty (Derivation body Θ (programGraph Q (newVals 1)
    (fun i => (stepTape H₁ K₁ i'₁ t'₁ a'₁ i).relabel k))) at q₂
  rw [tapeRename] at p₂ q₂
  have hi₂ := renameInto hi₁ k Θ preserve
  have ht₂ := renameInto ht₁ k Θ preserve
  have ha₂ := renameInto ha₁ k Θ preserve
  rw [axisRename] at hi₂ ht₂ ha₂
  have lp := ip body γ Θ ((oldVals 0).relabel k) (newVals 0) (H₁.relabel k) (K₁.relabel k)
    (i₁.relabel k) (i'₁.relabel k) (t₁.relabel k) (t'₁.relabel k) (a₁.relabel k) (a'₁.relabel k)
    p₁' p₂ hi₂ ht₂ ha₂
  have rq := iq body γ Θ ((oldVals 1).relabel k) (newVals 1) (H₁.relabel k) (K₁.relabel k)
    (i₁.relabel k) (i'₁.relabel k) (t₁.relabel k) (t'₁.relabel k) (a₁.relabel k) (a'₁.relabel k)
    q₁' q₂ hi₂ ht₂ ha₂
  exact exact_OpenOriginalAppendInclusion body γ Θ ((oldVals 0).relabel k) ((oldVals 1).relabel k)
    (newVals 0) (newVals 1) (o₁.relabel k) (n₁.relabel k) before' after lp rq

theorem includeNamed : OpenPartInclusion namedPart :=
  includeJoin freePart boundPart includeFree includeBound

theorem includeLeaves : OpenPartInclusion leavesPart :=
  includeJoin namedPart typePart includeNamed includeType

theorem includeThroughLambda : OpenPartInclusion throughLambda :=
  includeJoin leavesPart lambdaPart includeLeaves includeLambda

theorem includeThroughOrdinary : OpenPartInclusion throughOrdinary :=
  includeJoin throughLambda ordinaryPart includeThroughLambda includeOrdinary

theorem includeNonAux : OpenPartInclusion nonAuxPart :=
  includeJoin throughOrdinary numberedPart includeThroughOrdinary includeNumbered

theorem exact_OpenSelectedCoverTermPartInclusion : OpenPartInclusion termsPart :=
  includeJoin nonAuxPart auxiliaryPart includeNonAux includeAuxiliary

theorem exact_OpenSelectedCoverArgumentPartInclusion : OpenPartInclusion argsPart :=
  includeArgument

#print axioms exact_OpenSelectedCoverTermPartInclusion
#print axioms exact_OpenSelectedCoverArgumentPartInclusion

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorAppendProof
