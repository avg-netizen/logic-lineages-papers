module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLayerTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesInclusionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTransportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorAtomProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCoverAuxApplicationsOpenDataProof (recoverReordered)
open NumberedWindowInternalCoverAuxApplicationsTargets (auxApplications)
open NumberedWindowInternalCoverAuxLayerTransportProof (exact_OpenCoverAuxLayerTransport)
open NumberedWindowInternalCoverOrdinaryLayerTargets (ordinaryLayer)
open NumberedWindowInternalCoverOrdinaryLayerTransportProof (openTaggedLayerTransport exact_OpenCoverOrdinaryLayerTransport)
open NumberedWindowInternalCoverLambdaLayerTransportProof (exact_OpenCoverLambdaLayerTransport)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedLayer)
open NumberedWindowInternalCoverNumberedLayerTransportProof (exact_OpenCoverNumberedLayerTransport)
open NumberedWindowInternalCoverTypeLeavesTargets (typeLeaves unaryTape)
open NumberedWindowInternalCoverTypeLeavesInclusionProof (exact_OpenCoverTypeLeavesInclusion)
open NumberedWindowInternalCoverNamedLeavesTargets (namedFromIds)
open NumberedWindowInternalCoverArgumentCellsTargets (cellsAt)
open NumberedWindowInternalCoverArgumentCellsTransportProof (exact_OpenCoverArgumentCellsTransport)
open NumberedWindowInternalCoverSelectedSuccessorTargets
open NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem freeGraph (out H K ids ts args : OTerm α)
    (run : Nonempty (Derivation body Γ (stepReport freePart out H K ids ts args))) :
    Nonempty (Derivation body Γ (programGraph (namedFromIds 0) out (![K,ids]))) := by
  let xs := stepTape H K ids ts args
  let slots := (![1,2] : Fin 2 → Fin 5)
  have got := recoverReordered (namedFromIds 0) slots out xs run
  have same : (fun i => xs (slots i)) = ![K,ids] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  rw [same] at got
  exact got

private theorem boundGraph (out H K ids ts args : OTerm α)
    (run : Nonempty (Derivation body Γ (stepReport boundPart out H K ids ts args))) :
    Nonempty (Derivation body Γ (programGraph (namedFromIds 1) out (![K,ids]))) := by
  let xs := stepTape H K ids ts args
  let slots := (![1,2] : Fin 2 → Fin 5)
  have got := recoverReordered (namedFromIds 1) slots out xs run
  have same : (fun i => xs (slots i)) = ![K,ids] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  rw [same] at got
  exact got

private theorem typeGraph (out H K ids ts args : OTerm α)
    (run : Nonempty (Derivation body Γ (stepReport typePart out H K ids ts args))) :
    Nonempty (Derivation body Γ (programGraph typeLeaves out (unaryTape K))) := by
  let xs := stepTape H K ids ts args
  let slots := (![1] : Fin 1 → Fin 5)
  have got := recoverReordered typeLeaves slots out xs run
  have same : (fun i => xs (slots i)) = unaryTape K := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [same] at got
  exact got

private theorem lambdaGraph (out H K ids ts args : OTerm α)
    (run : Nonempty (Derivation body Γ (stepReport lambdaPart out H K ids ts args))) :
    Nonempty (Derivation body Γ (programGraph (namedFromIds 2) out (![K,ts]))) := by
  let xs := stepTape H K ids ts args
  let slots := (![1,3] : Fin 2 → Fin 5)
  have got := recoverReordered (namedFromIds 2) slots out xs run
  have same : (fun i => xs (slots i)) = ![K,ts] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  rw [same] at got
  exact got

private theorem ordinaryGraph (out H K ids ts args : OTerm α)
    (run : Nonempty (Derivation body Γ (stepReport ordinaryPart out H K ids ts args))) :
    Nonempty (Derivation body Γ (programGraph ordinaryLayer out (![H,args]))) := by
  let xs := stepTape H K ids ts args
  let slots := (![0,4] : Fin 2 → Fin 5)
  have got := recoverReordered ordinaryLayer slots out xs run
  have same : (fun i => xs (slots i)) = ![H,args] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  rw [same] at got
  exact got

private theorem numberedGraph (out H K ids ts args : OTerm α)
    (run : Nonempty (Derivation body Γ (stepReport numberedPart out H K ids ts args))) :
    Nonempty (Derivation body Γ (programGraph numberedLayer out (![H,K,ids,args]))) := by
  let xs := stepTape H K ids ts args
  let slots := (![0,1,2,4] : Fin 4 → Fin 5)
  have got := recoverReordered numberedLayer slots out xs run
  have same : (fun i => xs (slots i)) = ![H,K,ids,args] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.cases rfl (fun u => Fin.elim0 u) l) k) j) i
  rw [same] at got
  exact got

private theorem auxiliaryGraph (out H K ids ts args : OTerm α)
    (run : Nonempty (Derivation body Γ (stepReport auxiliaryPart out H K ids ts args))) :
    Nonempty (Derivation body Γ (programGraph auxApplications out (![K,ts]))) := by
  let xs := stepTape H K ids ts args
  let slots := (![1,3] : Fin 2 → Fin 5)
  have got := recoverReordered auxApplications slots out xs run
  have same : (fun i => xs (slots i)) = ![K,ts] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  rw [same] at got
  exact got

private theorem argumentGraph (out H K ids ts args : OTerm α)
    (run : Nonempty (Derivation body Γ (stepReport argsPart out H K ids ts args))) :
    Nonempty (Derivation body Γ (programGraph cellsAt out (![ts,args]))) := by
  let xs := stepTape H K ids ts args
  let slots := (![3,4] : Fin 2 → Fin 5)
  have got := recoverReordered cellsAt slots out xs run
  have same : (fun i => xs (slots i)) = ![ts,args] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  rw [same] at got
  exact got

theorem includeFree : OpenPartInclusion freePart := by
  apply includeOfAtKey freePart
  intro body α Γ old next H K ids ids' ts ts' args args' key small large hi ht ha hit
  exact openTaggedLayerTransport 0 body α Γ old next K ids ids' key
    (freeGraph old H K ids ts args small) (freeGraph next H K ids' ts' args' large)
    hi hit

theorem includeBound : OpenPartInclusion boundPart := by
  apply includeOfAtKey boundPart
  intro body α Γ old next H K ids ids' ts ts' args args' key small large hi ht ha hit
  exact openTaggedLayerTransport 1 body α Γ old next K ids ids' key
    (boundGraph old H K ids ts args small) (boundGraph next H K ids' ts' args' large)
    hi hit

theorem includeType : OpenPartInclusion typePart := by
  intro body α Γ old next H K ids ids' ts ts' args args' small large _ _ _
  exact exact_OpenCoverTypeLeavesInclusion body α Γ old next K
    (typeGraph old H K ids ts args small) (typeGraph next H K ids' ts' args' large)

theorem includeLambda : OpenPartInclusion lambdaPart := by
  apply includeOfAtKey lambdaPart
  intro body α Γ old next H K ids ids' ts ts' args args' key small large hi ht ha hit
  exact exact_OpenCoverLambdaLayerTransport body α Γ old next K ts ts' key
    (lambdaGraph old H K ids ts args small) (lambdaGraph next H K ids' ts' args' large)
    ht hit

theorem includeOrdinary : OpenPartInclusion ordinaryPart := by
  apply includeOfAtKey ordinaryPart
  intro body α Γ old next H K ids ids' ts ts' args args' key small large hi ht ha hit
  exact exact_OpenCoverOrdinaryLayerTransport body α Γ old next H args args' key
    (ordinaryGraph old H K ids ts args small) (ordinaryGraph next H K ids' ts' args' large)
    ha hit

theorem includeNumbered : OpenPartInclusion numberedPart := by
  apply includeOfAtKey numberedPart
  intro body α Γ old next H K ids ids' ts ts' args args' key small large hi ht ha hit
  exact exact_OpenCoverNumberedLayerTransport body α Γ old next H K ids ids' args args' key
    (numberedGraph old H K ids ts args small) (numberedGraph next H K ids' ts' args' large)
    hi ha hit

theorem includeAuxiliary : OpenPartInclusion auxiliaryPart := by
  apply includeOfAtKey auxiliaryPart
  intro body α Γ old next H K ids ids' ts ts' args args' key small large hi ht ha hit
  exact exact_OpenCoverAuxLayerTransport body α Γ old next K ts ts' key
    (auxiliaryGraph old H K ids ts args small) (auxiliaryGraph next H K ids' ts' args' large)
    ht hit

theorem includeArgument : OpenPartInclusion argsPart := by
  apply includeOfAtKey argsPart
  intro body α Γ old next H K ids ids' ts ts' args args' key small large hi ht ha hit
  exact exact_OpenCoverArgumentCellsTransport body α Γ old next ts ts' args args' key
    (argumentGraph old H K ids ts args small) (argumentGraph next H K ids' ts' args' large)
    ht ha hit

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorAtomProof
