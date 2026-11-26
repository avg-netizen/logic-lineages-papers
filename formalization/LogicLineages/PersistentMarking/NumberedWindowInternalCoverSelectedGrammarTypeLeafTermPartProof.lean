module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarTypeLeafTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesConstructorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarTypeLeafTermPartProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCompositionCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCoverAuxApplicationsOpenDataProof (recoverReordered)
open NumberedWindowInternalCoverTypeLeavesTargets (typeLeaves typeLeafTerm unaryTape typeLeavesReport)
open NumberedWindowInternalCoverTypeLeavesOpenDataProof (termRename)
open NumberedWindowInternalCoverTypeLeavesConstructorProof (exact_OpenCoverTypeLeavesConstructor)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalScratchAppendOpenChecks (fromLeft fromRight)
open NumberedWindowInternalCoverSelectedSuccessorTargets
open NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof (tapeRename)
open NumberedWindowInternalCoverSelectedGrammarTypeLeafTargets

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

private theorem immediate : OpenSelectedPartContainsTypeLeaf typePart := by
  intro body α Γ out H K ids terms args ty actual ht
  let xs := stepTape H K ids terms args
  let slots := (![1] : Fin 1 → Fin 5)
  have got := recoverReordered typeLeaves slots out xs actual
  have same : (fun i => xs (slots i)) = unaryTape K := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [same] at got
  exact exact_OpenCoverTypeLeavesConstructor body α Γ out K ty got ht

private theorem inLeft (P Q : Program 5) (p : OpenSelectedPartContainsTypeLeaf P) :
    OpenSelectedPartContainsTypeLeaf (join P Q) := by
  intro body α Γ out H K ids terms args ty actual ht
  let sels : Fin 2 → Program 5 := Fin.cons P (Fin.cons Q Fin.elim0)
  apply programCompositionCases append sels out (stepTape H K ids terms args) _ actual
  intro β j ys Δ keep appended reports
  rw [graphRename,termRename]
  have sub := reports 0
  change Nonempty (Derivation body Δ (programGraph P (ys 0)
    (fun i => (stepTape H K ids terms args i).relabel j))) at sub
  rw [tapeRename] at sub
  have ht' := renameInto ht j Δ keep
  rw [graphRename] at ht'
  have hit := p body β Δ (ys 0) (H.relabel j) (K.relabel j) (ids.relabel j)
    (terms.relabel j) (args.relabel j) (ty.relabel j) sub ht'
  exact fromLeft (ys 0) (ys 1) (out.relabel j) (typeLeafTerm (ty.relabel j))
    (appendTape (out.relabel j) ys appended) hit

private theorem inRight (P Q : Program 5) (q : OpenSelectedPartContainsTypeLeaf Q) :
    OpenSelectedPartContainsTypeLeaf (join P Q) := by
  intro body α Γ out H K ids terms args ty actual ht
  let sels : Fin 2 → Program 5 := Fin.cons P (Fin.cons Q Fin.elim0)
  apply programCompositionCases append sels out (stepTape H K ids terms args) _ actual
  intro β j ys Δ keep appended reports
  rw [graphRename,termRename]
  have sub := reports 1
  change Nonempty (Derivation body Δ (programGraph Q (ys 1)
    (fun i => (stepTape H K ids terms args i).relabel j))) at sub
  rw [tapeRename] at sub
  have ht' := renameInto ht j Δ keep
  rw [graphRename] at ht'
  have hit := q body β Δ (ys 1) (H.relabel j) (K.relabel j) (ids.relabel j)
    (terms.relabel j) (args.relabel j) (ty.relabel j) sub ht'
  exact fromRight (ys 0) (ys 1) (out.relabel j) (typeLeafTerm (ty.relabel j))
    (appendTape (out.relabel j) ys appended) hit

theorem exact_OpenSelectedTypeLeafInTermPart : OpenSelectedPartContainsTypeLeaf termsPart :=
  inLeft nonAuxPart auxiliaryPart
    (inLeft throughOrdinary numberedPart
      (inLeft throughLambda ordinaryPart
        (inLeft leavesPart lambdaPart (inRight namedPart typePart immediate))))

#print axioms exact_OpenSelectedTypeLeafInTermPart

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarTypeLeafTermPartProof
