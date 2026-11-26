module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerConstructorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCompositionCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCoverAuxApplicationsOpenDataProof (recoverReordered)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaLayer lambdaTerm)
open NumberedWindowInternalCoverNamedLeavesOpenDataProof (namedRename)
open NumberedWindowInternalCoverLambdaLayerConstructorProof (exact_OpenCoverLambdaLayerConstructor)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalScratchAppendOpenChecks (fromLeft fromRight)
open NumberedWindowInternalCoverSelectedSuccessorTargets
open NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof (tapeRename)
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnTargets

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

private theorem immediate : OpenSelectedPartContainsLambda lambdaPart := by
  intro body α Γ out H K ids terms args ty q actual ht hq
  let xs := stepTape H K ids terms args
  let slots := (![1,3] : Fin 2 → Fin 5)
  have got := recoverReordered lambdaLayer slots out xs actual
  have same : (fun i => xs (slots i)) = ![K,terms] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  rw [same] at got
  exact exact_OpenCoverLambdaLayerConstructor body α Γ out K terms ty q got ht hq

theorem lambdaRename {β : Type} (ty q : OTerm α) (j : α → β) :
    (lambdaTerm ty q).relabel j = lambdaTerm (ty.relabel j) (q.relabel j) :=
  namedRename 2 ty q j

private theorem inLeft (P Q : Program 5) (p : OpenSelectedPartContainsLambda P) :
    OpenSelectedPartContainsLambda (join P Q) := by
  intro body α Γ out H K ids terms args ty q actual ht hq
  let sels : Fin 2 → Program 5 := Fin.cons P (Fin.cons Q Fin.elim0)
  apply programCompositionCases append sels out (stepTape H K ids terms args) _ actual
  intro β j ys Δ keep appended reports
  rw [graphRename,lambdaRename]
  have sub := reports 0
  change Nonempty (Derivation body Δ (programGraph P (ys 0)
    (fun i => (stepTape H K ids terms args i).relabel j))) at sub
  rw [tapeRename] at sub
  have ht' := renameInto ht j Δ keep
  have hq' := renameInto hq j Δ keep
  rw [graphRename] at ht' hq'
  have hit := p body β Δ (ys 0) (H.relabel j) (K.relabel j) (ids.relabel j)
    (terms.relabel j) (args.relabel j) (ty.relabel j) (q.relabel j) sub ht' hq'
  exact fromLeft (ys 0) (ys 1) (out.relabel j) (lambdaTerm (ty.relabel j) (q.relabel j))
    (appendTape (out.relabel j) ys appended) hit

private theorem inRight (P Q : Program 5) (inside : OpenSelectedPartContainsLambda Q) :
    OpenSelectedPartContainsLambda (join P Q) := by
  intro body α Γ out H K ids terms args ty q actual ht hq
  let sels : Fin 2 → Program 5 := Fin.cons P (Fin.cons Q Fin.elim0)
  apply programCompositionCases append sels out (stepTape H K ids terms args) _ actual
  intro β j ys Δ keep appended reports
  rw [graphRename,lambdaRename]
  have sub := reports 1
  change Nonempty (Derivation body Δ (programGraph Q (ys 1)
    (fun i => (stepTape H K ids terms args i).relabel j))) at sub
  rw [tapeRename] at sub
  have ht' := renameInto ht j Δ keep
  have hq' := renameInto hq j Δ keep
  rw [graphRename] at ht' hq'
  have hit := inside body β Δ (ys 1) (H.relabel j) (K.relabel j) (ids.relabel j)
    (terms.relabel j) (args.relabel j) (ty.relabel j) (q.relabel j) sub ht' hq'
  exact fromRight (ys 0) (ys 1) (out.relabel j) (lambdaTerm (ty.relabel j) (q.relabel j))
    (appendTape (out.relabel j) ys appended) hit

theorem exact_OpenSelectedLambdaInTermPart : OpenSelectedPartContainsLambda termsPart :=
  inLeft nonAuxPart auxiliaryPart
    (inLeft throughOrdinary numberedPart
      (inLeft throughLambda ordinaryPart (inRight leavesPart lambdaPart immediate)))

#print axioms exact_OpenSelectedLambdaInTermPart

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof
