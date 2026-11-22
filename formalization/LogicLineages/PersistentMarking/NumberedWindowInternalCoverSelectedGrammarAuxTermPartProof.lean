module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxParentTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsThinOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxTermPartProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCompositionCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCoverAuxApplicationsTargets (auxApplications)
open NumberedWindowInternalCoverAuxApplicationsOpenDataProof (recoverReordered)
open NumberedWindowInternalCoverAuxApplicationsThinOpenProof (exact_OpenAuxApplicationsMember)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalScratchAppendOpenChecks (fromRight)
open NumberedWindowInternalCoverSelectedSuccessorTargets
open NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof (tapeRename)
open NumberedWindowInternalCoverSelectedGrammarAuxParentTargets

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

private theorem recoverAux (out H K ids terms args : OTerm α)
    (run : Nonempty (Derivation body Γ (stepReport auxiliaryPart out H K ids terms args))) :
    Nonempty (Derivation body Γ (programGraph auxApplications out ![K,terms])) := by
  let xs := stepTape H K ids terms args
  let slots : Fin 2 → Fin 5 := ![1,3]
  have moved := recoverReordered auxApplications slots out xs run
  have tape : (fun i => xs (slots i)) = ![K,terms] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  rw [tape] at moved
  exact moved

theorem exact_OpenSelectedAuxInTermPart : ExactOpenSelectedAuxInTermPart := by
  intro body α Γ out H K ids terms args dom cod fn arg run hd hc hf ha
  let sels : Fin 2 → Program 5 := Fin.cons nonAuxPart (Fin.cons auxiliaryPart Fin.elim0)
  apply programCompositionCases append sels out (stepTape H K ids terms args) _ run
  intro β j ys Δ keep appended reports
  rw [graphRename,auxiliaryRename]
  have components := reports 1
  change Nonempty (Derivation body Δ (programGraph auxiliaryPart (ys 1)
    (fun i => (stepTape H K ids terms args i).relabel j))) at components
  rw [tapeRename] at components
  have aux := recoverAux (ys 1) (H.relabel j) (K.relabel j) (ids.relabel j)
    (terms.relabel j) (args.relabel j) components
  have hd' := renameInto hd j Δ keep
  have hc' := renameInto hc j Δ keep
  have hf' := renameInto hf j Δ keep
  have ha' := renameInto ha j Δ keep
  rw [graphRename] at hd' hc' hf' ha'
  let key := auxiliaryTerm (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
  have occurs := exact_OpenAuxApplicationsMember body β Δ (K.relabel j) (terms.relabel j)
    (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) (ys 1)
    hd' hc' hf' ha' aux
  exact fromRight (ys 0) (ys 1) (out.relabel j) key (appendTape (out.relabel j) ys appended) occurs

#print axioms exact_OpenSelectedAuxInTermPart

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxTermPartProof
