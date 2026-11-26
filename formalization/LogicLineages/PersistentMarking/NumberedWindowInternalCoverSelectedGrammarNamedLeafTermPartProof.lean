module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNamedLeafTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesFromIdsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNamedLeafTermPartProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCompositionCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCoverAuxApplicationsOpenDataProof (recoverReordered)
open NumberedWindowInternalCoverNamedLeavesTargets (namedFromIds typeBlock namedTerm)
open NumberedWindowInternalCoverNamedLeavesOpenDataProof (namedRename)
open NumberedWindowInternalCoverNamedLeavesFromIdsProof (exact_OpenCoverNamedFromIdsMember)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalScratchAppendOpenChecks (fromLeft fromRight)
open NumberedWindowInternalCoverSelectedSuccessorTargets
open NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof (tapeRename)
open NumberedWindowInternalCoverSelectedGrammarNamedLeafTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem appendTape (out : OTerm α) (ys : Fin 2 → OTerm α)
    (run : Nonempty (Derivation body Γ (programGraph append out ys))) :
    Nonempty (Derivation body Γ (appendGraph out (ys 0) (ys 1))) := by
  have same : ys = ![ys 0,ys 1] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  rw [same] at run
  exact run

private theorem actualBranch (b : Bool) :
    selectedNamedPart b = NumberedWindowInternalCoverAuxApplicationsTargets.reorder
      (namedFromIds b.toNat) (![1,2] : Fin 2 → Fin 5) := by
  cases b <;> rfl

private theorem immediate (b : Bool) : OpenSelectedPartContainsNamedLeaf b (selectedNamedPart b) := by
  intro body α Γ out H K ids terms args ty i actual ht hi
  let xs := stepTape H K ids terms args
  let slots := (![1,2] : Fin 2 → Fin 5)
  rw [actualBranch] at actual
  have got := recoverReordered (namedFromIds b.toNat) slots out xs actual
  have same : (fun i => xs (slots i)) = ![K,ids] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  rw [same] at got
  exact exact_OpenCoverNamedFromIdsMember b.toNat K ty i ids out ht hi got

private theorem inLeft (b : Bool) (P Q : Program 5) (p : OpenSelectedPartContainsNamedLeaf b P) :
    OpenSelectedPartContainsNamedLeaf b (join P Q) := by
  intro body α Γ out H K ids terms args ty i actual ht hi
  let sels : Fin 2 → Program 5 := Fin.cons P (Fin.cons Q Fin.elim0)
  apply programCompositionCases append sels out (stepTape H K ids terms args) _ actual
  intro β j ys Δ keep appended reports
  rw [graphRename,namedRename]
  have sub := reports 0
  change Nonempty (Derivation body Δ (programGraph P (ys 0)
    (fun i => (stepTape H K ids terms args i).relabel j))) at sub
  rw [tapeRename] at sub
  have ht' := renameInto ht j Δ keep
  have hi' := renameInto hi j Δ keep
  rw [graphRename] at ht' hi'
  have hit := p body β Δ (ys 0) (H.relabel j) (K.relabel j) (ids.relabel j)
    (terms.relabel j) (args.relabel j) (ty.relabel j) (i.relabel j) sub ht' hi'
  exact fromLeft (ys 0) (ys 1) (out.relabel j) (namedTerm b.toNat (ty.relabel j) (i.relabel j))
    (appendTape (out.relabel j) ys appended) hit

private theorem inRight (b : Bool) (P Q : Program 5) (q : OpenSelectedPartContainsNamedLeaf b Q) :
    OpenSelectedPartContainsNamedLeaf b (join P Q) := by
  intro body α Γ out H K ids terms args ty i actual ht hi
  let sels : Fin 2 → Program 5 := Fin.cons P (Fin.cons Q Fin.elim0)
  apply programCompositionCases append sels out (stepTape H K ids terms args) _ actual
  intro β j ys Δ keep appended reports
  rw [graphRename,namedRename]
  have sub := reports 1
  change Nonempty (Derivation body Δ (programGraph Q (ys 1)
    (fun i => (stepTape H K ids terms args i).relabel j))) at sub
  rw [tapeRename] at sub
  have ht' := renameInto ht j Δ keep
  have hi' := renameInto hi j Δ keep
  rw [graphRename] at ht' hi'
  have hit := q body β Δ (ys 1) (H.relabel j) (K.relabel j) (ids.relabel j)
    (terms.relabel j) (args.relabel j) (ty.relabel j) (i.relabel j) sub ht' hi'
  exact fromRight (ys 0) (ys 1) (out.relabel j) (namedTerm b.toNat (ty.relabel j) (i.relabel j))
    (appendTape (out.relabel j) ys appended) hit

private theorem inNamed (b : Bool) : OpenSelectedPartContainsNamedLeaf b namedPart := by
  cases b
  · exact inLeft false freePart boundPart (immediate false)
  · exact inRight true freePart boundPart (immediate true)

theorem exact_OpenSelectedNamedLeafInTermPart (b : Bool) : OpenSelectedPartContainsNamedLeaf b termsPart :=
  inLeft b nonAuxPart auxiliaryPart
    (inLeft b throughOrdinary numberedPart
      (inLeft b throughLambda ordinaryPart
        (inLeft b leavesPart lambdaPart (inLeft b namedPart typePart (inNamed b)))))

#print axioms exact_OpenSelectedNamedLeafInTermPart

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNamedLeafTermPartProof
