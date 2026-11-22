module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNullaryTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerConstructorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNullaryTermPartProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCompositionCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ID1Completion.InternalTagArithmeticSyntaxProof (z zRelabel)
open NumberedWindowInternalCoverAuxApplicationsOpenDataProof (recoverReordered)
open NumberedWindowInternalCoverOrdinaryLayerTargets (ordinaryLayer)
open NumberedWindowInternalCoverNamedLeavesOpenDataProof (namedRename)
open NumberedWindowInternalCoverOrdinaryLayerConstructorProof (exact_OpenCoverOrdinaryLayerConstructor)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalScratchAppendOpenChecks (fromLeft fromRight)
open NumberedWindowInternalCoverSelectedSuccessorTargets
open NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof (tapeRename)
open NumberedWindowInternalCoverSelectedGrammarNullaryTargets

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

private theorem immediate : OpenSelectedPartContainsNullary ordinaryPart := by
  intro body α Γ out H K ids terms args h actual head zero
  let xs := stepTape H K ids terms args
  let slots := (![0,4] : Fin 2 → Fin 5)
  have got := recoverReordered ordinaryLayer slots out xs actual
  have same : (fun i => xs (slots i)) = ![H,args] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  rw [same] at got
  exact exact_OpenCoverOrdinaryLayerConstructor body α Γ out H args h z got head zero

theorem nullaryRename {β : Type} (h : OTerm α) (j : α → β) :
    (nullaryKey h).relabel j = nullaryKey (h.relabel j) := by
  simp only [nullaryKey,NumberedWindowInternalCoverOrdinaryLayerTargets.taggedTerm,namedRename,zRelabel]

private theorem inLeft (P Q : Program 5) (p : OpenSelectedPartContainsNullary P) :
    OpenSelectedPartContainsNullary (join P Q) := by
  intro body α Γ out H K ids terms args h actual head zero
  let sels : Fin 2 → Program 5 := Fin.cons P (Fin.cons Q Fin.elim0)
  apply programCompositionCases append sels out (stepTape H K ids terms args) _ actual
  intro β j ys Δ keep appended reports
  rw [graphRename,nullaryRename]
  have sub := reports 0
  change Nonempty (Derivation body Δ (programGraph P (ys 0)
    (fun i => (stepTape H K ids terms args i).relabel j))) at sub
  rw [tapeRename] at sub
  have head' := renameInto head j Δ keep
  have zero' := renameInto zero j Δ keep
  rw [graphRename] at head'
  simp only [graphRename,zRelabel] at zero'
  have hit := p body β Δ (ys 0) (H.relabel j) (K.relabel j) (ids.relabel j)
    (terms.relabel j) (args.relabel j) (h.relabel j) sub head' zero'
  exact fromLeft (ys 0) (ys 1) (out.relabel j) (nullaryKey (h.relabel j))
    (appendTape (out.relabel j) ys appended) hit

private theorem inRight (P Q : Program 5) (q : OpenSelectedPartContainsNullary Q) :
    OpenSelectedPartContainsNullary (join P Q) := by
  intro body α Γ out H K ids terms args h actual head zero
  let sels : Fin 2 → Program 5 := Fin.cons P (Fin.cons Q Fin.elim0)
  apply programCompositionCases append sels out (stepTape H K ids terms args) _ actual
  intro β j ys Δ keep appended reports
  rw [graphRename,nullaryRename]
  have sub := reports 1
  change Nonempty (Derivation body Δ (programGraph Q (ys 1)
    (fun i => (stepTape H K ids terms args i).relabel j))) at sub
  rw [tapeRename] at sub
  have head' := renameInto head j Δ keep
  have zero' := renameInto zero j Δ keep
  rw [graphRename] at head'
  simp only [graphRename,zRelabel] at zero'
  have hit := q body β Δ (ys 1) (H.relabel j) (K.relabel j) (ids.relabel j)
    (terms.relabel j) (args.relabel j) (h.relabel j) sub head' zero'
  exact fromRight (ys 0) (ys 1) (out.relabel j) (nullaryKey (h.relabel j))
    (appendTape (out.relabel j) ys appended) hit

theorem exact_OpenSelectedNullaryInTermPart : OpenSelectedPartContainsNullary termsPart :=
  inLeft nonAuxPart auxiliaryPart
    (inLeft throughOrdinary numberedPart (inRight throughLambda ordinaryPart immediate))

#print axioms exact_OpenSelectedNullaryInTermPart

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNullaryTermPartProof
