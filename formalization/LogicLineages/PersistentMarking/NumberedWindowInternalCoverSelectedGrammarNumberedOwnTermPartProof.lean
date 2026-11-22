module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerConstructorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnTermPartProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCompositionCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCoverAuxApplicationsOpenDataProof (recoverReordered)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedLayer numberedTerm)
open NumberedWindowInternalCoverNumberedLayerOpenDataProof (numberedRename)
open NumberedWindowInternalCoverNumberedLayerConstructorProof (exact_OpenCoverNumberedLayerConstructor)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalScratchAppendOpenChecks (fromLeft fromRight)
open NumberedWindowInternalCoverSelectedSuccessorTargets
open NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof (tapeRename)
open NumberedWindowInternalCoverSelectedGrammarNumberedOwnTargets

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

private theorem immediate : OpenSelectedPartContainsNumbered numberedPart := by
  intro body α Γ out H K ids terms args h ty k l r actual head type id left right
  let xs := stepTape H K ids terms args
  let slots := (![0,1,2,4] : Fin 4 → Fin 5)
  have got := recoverReordered numberedLayer slots out xs actual
  have same : (fun i => xs (slots i)) = ![H,K,ids,args] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl
      (fun l => Fin.cases rfl (fun u => Fin.elim0 u) l) k) j) i
  rw [same] at got
  exact exact_OpenCoverNumberedLayerConstructor body α Γ out H K ids args h ty k l r
    got head type id left right

private theorem inLeft (P Q : Program 5) (p : OpenSelectedPartContainsNumbered P) :
    OpenSelectedPartContainsNumbered (join P Q) := by
  intro body α Γ out H K ids terms args h ty k l r actual head type id left right
  let sels : Fin 2 → Program 5 := Fin.cons P (Fin.cons Q Fin.elim0)
  apply programCompositionCases append sels out (stepTape H K ids terms args) _ actual
  intro β j ys Δ keep appended reports
  rw [graphRename,numberedRename]
  have sub := reports 0
  change Nonempty (Derivation body Δ (programGraph P (ys 0)
    (fun i => (stepTape H K ids terms args i).relabel j))) at sub
  rw [tapeRename] at sub
  have head' := renameInto head j Δ keep
  have type' := renameInto type j Δ keep
  have id' := renameInto id j Δ keep
  have left' := renameInto left j Δ keep
  have right' := renameInto right j Δ keep
  rw [graphRename] at head' type' id' left' right'
  have hit := p body β Δ (ys 0) (H.relabel j) (K.relabel j) (ids.relabel j)
    (terms.relabel j) (args.relabel j) (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j)
    sub head' type' id' left' right'
  exact fromLeft (ys 0) (ys 1) (out.relabel j) (numberedTerm (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j))
    (appendTape (out.relabel j) ys appended) hit

private theorem inRight (P Q : Program 5) (q : OpenSelectedPartContainsNumbered Q) :
    OpenSelectedPartContainsNumbered (join P Q) := by
  intro body α Γ out H K ids terms args h ty k l r actual head type id left right
  let sels : Fin 2 → Program 5 := Fin.cons P (Fin.cons Q Fin.elim0)
  apply programCompositionCases append sels out (stepTape H K ids terms args) _ actual
  intro β j ys Δ keep appended reports
  rw [graphRename,numberedRename]
  have sub := reports 1
  change Nonempty (Derivation body Δ (programGraph Q (ys 1)
    (fun i => (stepTape H K ids terms args i).relabel j))) at sub
  rw [tapeRename] at sub
  have head' := renameInto head j Δ keep
  have type' := renameInto type j Δ keep
  have id' := renameInto id j Δ keep
  have left' := renameInto left j Δ keep
  have right' := renameInto right j Δ keep
  rw [graphRename] at head' type' id' left' right'
  have hit := q body β Δ (ys 1) (H.relabel j) (K.relabel j) (ids.relabel j)
    (terms.relabel j) (args.relabel j) (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j)
    sub head' type' id' left' right'
  exact fromRight (ys 0) (ys 1) (out.relabel j) (numberedTerm (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j))
    (appendTape (out.relabel j) ys appended) hit

theorem exact_OpenSelectedNumberedInTermPart : OpenSelectedPartContainsNumbered termsPart :=
  inLeft nonAuxPart auxiliaryPart
    (inRight throughOrdinary numberedPart immediate)

#print axioms exact_OpenSelectedNumberedInTermPart

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnTermPartProof
