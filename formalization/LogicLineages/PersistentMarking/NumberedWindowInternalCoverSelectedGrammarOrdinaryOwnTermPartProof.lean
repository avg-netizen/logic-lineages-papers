module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerConstructorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTermPartProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCompositionCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCoverAuxApplicationsOpenDataProof (recoverReordered)
open NumberedWindowInternalCoverOrdinaryLayerTargets (ordinaryLayer)
open NumberedWindowInternalCoverNamedLeavesOpenDataProof (namedRename)
open NumberedWindowInternalCoverOrdinaryLayerConstructorProof (exact_OpenCoverOrdinaryLayerConstructor)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalScratchAppendOpenChecks (fromLeft fromRight)
open NumberedWindowInternalCoverSelectedSuccessorTargets
open NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof (tapeRename)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets

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

private theorem immediate : OpenSelectedPartContainsOrdinary ordinaryPart := by
  intro body α Γ out H K ids terms args h a actual head arg
  let xs := stepTape H K ids terms args
  let slots := (![0,4] : Fin 2 → Fin 5)
  have got := recoverReordered ordinaryLayer slots out xs actual
  have same : (fun i => xs (slots i)) = ![H,args] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  rw [same] at got
  exact exact_OpenCoverOrdinaryLayerConstructor body α Γ out H args h a got head arg

theorem ordinaryRename {β : Type} (h a : OTerm α) (j : α → β) :
    (ordinaryKey h a).relabel j = ordinaryKey (h.relabel j) (a.relabel j) :=
  namedRename 4 h a j

private theorem inLeft (P Q : Program 5) (p : OpenSelectedPartContainsOrdinary P) :
    OpenSelectedPartContainsOrdinary (join P Q) := by
  intro body α Γ out H K ids terms args h a actual head arg
  let sels : Fin 2 → Program 5 := Fin.cons P (Fin.cons Q Fin.elim0)
  apply programCompositionCases append sels out (stepTape H K ids terms args) _ actual
  intro β j ys Δ keep appended reports
  rw [graphRename,ordinaryRename]
  have sub := reports 0
  change Nonempty (Derivation body Δ (programGraph P (ys 0)
    (fun i => (stepTape H K ids terms args i).relabel j))) at sub
  rw [tapeRename] at sub
  have head' := renameInto head j Δ keep
  have arg' := renameInto arg j Δ keep
  rw [graphRename] at head' arg'
  have hit := p body β Δ (ys 0) (H.relabel j) (K.relabel j) (ids.relabel j)
    (terms.relabel j) (args.relabel j) (h.relabel j) (a.relabel j) sub head' arg'
  exact fromLeft (ys 0) (ys 1) (out.relabel j) (ordinaryKey (h.relabel j) (a.relabel j))
    (appendTape (out.relabel j) ys appended) hit

private theorem inRight (P Q : Program 5) (q : OpenSelectedPartContainsOrdinary Q) :
    OpenSelectedPartContainsOrdinary (join P Q) := by
  intro body α Γ out H K ids terms args h a actual head arg
  let sels : Fin 2 → Program 5 := Fin.cons P (Fin.cons Q Fin.elim0)
  apply programCompositionCases append sels out (stepTape H K ids terms args) _ actual
  intro β j ys Δ keep appended reports
  rw [graphRename,ordinaryRename]
  have sub := reports 1
  change Nonempty (Derivation body Δ (programGraph Q (ys 1)
    (fun i => (stepTape H K ids terms args i).relabel j))) at sub
  rw [tapeRename] at sub
  have head' := renameInto head j Δ keep
  have arg' := renameInto arg j Δ keep
  rw [graphRename] at head' arg'
  have hit := q body β Δ (ys 1) (H.relabel j) (K.relabel j) (ids.relabel j)
    (terms.relabel j) (args.relabel j) (h.relabel j) (a.relabel j) sub head' arg'
  exact fromRight (ys 0) (ys 1) (out.relabel j) (ordinaryKey (h.relabel j) (a.relabel j))
    (appendTape (out.relabel j) ys appended) hit

theorem exact_OpenSelectedOrdinaryInTermPart : OpenSelectedPartContainsOrdinary termsPart :=
  inLeft nonAuxPart auxiliaryPart
    (inLeft throughOrdinary numberedPart (inRight throughLambda ordinaryPart immediate))

#print axioms exact_OpenSelectedOrdinaryInTermPart

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTermPartProof
