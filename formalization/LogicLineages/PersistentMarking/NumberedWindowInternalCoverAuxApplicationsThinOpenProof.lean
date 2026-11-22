module
/- Thin arbitrary-open derivation recut of NumberedWindowInternalCoverAuxApplicationsChecks; original statement and physical programs unchanged. -/

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldThinOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsThinOpenProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (consTermRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalCoverCartesianFoldTargets (flatMap flatGraph)
open NumberedWindowInternalCoverCartesianFoldSyntaxProof (flatRename)
open NumberedWindowInternalCoverCartesianFoldThinOpenProof (exact_OpenCartesianFoldMember)
open NumberedWindowInternalCoverAuxApplicationsTargets
open NumberedWindowInternalCoverAuxApplicationsOpenDataProof (recoverReordered singletonMember)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem liftMember {k : Nat} (D : Program (k+1)) (raw source image out : OTerm α)
    (params : Fin k → OTerm α)
    (sourceMember : Nonempty (Derivation body Γ (memberGraph raw source)))
    (actual : Nonempty (Derivation body Γ (flatGraph D out raw params)))
    (inner : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (block : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (programGraph D block (Fin.cons (source.relabel j) (fun i => (params i).relabel j)))) →
      Nonempty (Derivation body Δ (memberGraph block (image.relabel j)))) :
    Nonempty (Derivation body Γ (memberGraph out image)) := by
  apply programCases D (Fin.cons source params) _
  intro β j Δ block keep report
  rw [graphRename]
  simp only [consTermRename] at report
  have member := renameInto sourceMember j Δ keep
  have result := renameInto actual j Δ keep
  simp only [graphRename] at member
  simp only [flatRename] at result
  exact exact_OpenCartesianFoldMember D body β Δ (raw.relabel j) (source.relabel j) block (image.relabel j)
    (out.relabel j) (fun i => (params i).relabel j) member report (inner β j Δ block keep report) result

private theorem fromArgAxis (T d c f a out : OTerm α)
    (argIn : Nonempty (Derivation body Γ (memberGraph T a)))
    (actual : Nonempty (Derivation body Γ (programGraph argAxis out ![f,T,d,c]))) :
    Nonempty (Derivation body Γ (memberGraph out (auxiliaryTerm d c f a))) := by
  let xs : Fin 4 → OTerm α := ![f,T,d,c]
  let slots : Fin 4 → Fin 4 := ![1,2,3,0]
  let p : Fin 3 → OTerm α := ![d,c,f]
  have decoded := recoverReordered (flatMap singletonAux) slots out xs actual
  have tape : (fun i => xs (slots i)) = Fin.cons T p := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))) i
  rw [tape] at decoded
  apply liftMember singletonAux T a (auxiliaryTerm d c f a) out p argIn decoded
  intro β j Δ block _ report
  rw [auxiliaryRename]
  have same : (Fin.cons (a.relabel j) (fun i => (p i).relabel j) : Fin 4 → OTerm β) =
      ![a.relabel j,d.relabel j,c.relabel j,f.relabel j] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))) i
  rw [same] at report
  exact singletonMember (d.relabel j) (c.relabel j) (f.relabel j) (a.relabel j) block report

private theorem fromFnAxis (K T d c f a out : OTerm α)
    (fnIn : Nonempty (Derivation body Γ (memberGraph T f)))
    (argIn : Nonempty (Derivation body Γ (memberGraph T a)))
    (actual : Nonempty (Derivation body Γ (programGraph fnAxis out ![c,K,T,d]))) :
    Nonempty (Derivation body Γ (memberGraph out (auxiliaryTerm d c f a))) := by
  let xs : Fin 4 → OTerm α := ![c,K,T,d]
  let slots : Fin 4 → Fin 4 := ![2,2,3,0]
  let p : Fin 3 → OTerm α := ![T,d,c]
  have decoded := recoverReordered (flatMap argAxis) slots out xs actual
  have tape : (fun i => xs (slots i)) = Fin.cons T p := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))) i
  rw [tape] at decoded
  apply liftMember argAxis T f (auxiliaryTerm d c f a) out p fnIn decoded
  intro β j Δ block keep report
  rw [auxiliaryRename]
  have arg := renameInto argIn j Δ keep
  simp only [graphRename] at arg
  have same : (Fin.cons (f.relabel j) (fun i => (p i).relabel j) : Fin 4 → OTerm β) =
      ![f.relabel j,T.relabel j,d.relabel j,c.relabel j] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))) i
  rw [same] at report
  exact fromArgAxis (T.relabel j) (d.relabel j) (c.relabel j) (f.relabel j) (a.relabel j) block arg report

private theorem fromCodAxis (K T d c f a out : OTerm α)
    (codIn : Nonempty (Derivation body Γ (memberGraph K c)))
    (fnIn : Nonempty (Derivation body Γ (memberGraph T f)))
    (argIn : Nonempty (Derivation body Γ (memberGraph T a)))
    (actual : Nonempty (Derivation body Γ (programGraph codAxis out ![d,K,T]))) :
    Nonempty (Derivation body Γ (memberGraph out (auxiliaryTerm d c f a))) := by
  let xs : Fin 3 → OTerm α := ![d,K,T]
  let slots : Fin 4 → Fin 3 := ![1,1,2,0]
  let p : Fin 3 → OTerm α := ![K,T,d]
  have decoded := recoverReordered (flatMap fnAxis) slots out xs actual
  have tape : (fun i => xs (slots i)) = Fin.cons K p := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))) i
  rw [tape] at decoded
  apply liftMember fnAxis K c (auxiliaryTerm d c f a) out p codIn decoded
  intro β j Δ block keep report
  rw [auxiliaryRename]
  have fn := renameInto fnIn j Δ keep
  have arg := renameInto argIn j Δ keep
  simp only [graphRename] at fn arg
  have same : (Fin.cons (c.relabel j) (fun i => (p i).relabel j) : Fin 4 → OTerm β) =
      ![c.relabel j,K.relabel j,T.relabel j,d.relabel j] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))) i
  rw [same] at report
  exact fromFnAxis (K.relabel j) (T.relabel j) (d.relabel j) (c.relabel j) (f.relabel j) (a.relabel j) block fn arg report

theorem exact_OpenAuxApplicationsMember : ExactOpenAuxApplicationsMember := by
  intro body α Γ K T d c f a out domIn codIn fnIn argIn actual
  let xs : Fin 2 → OTerm α := ![K,T]
  let slots : Fin 3 → Fin 2 := ![0,0,1]
  let p : Fin 2 → OTerm α := ![K,T]
  have decoded := recoverReordered (flatMap codAxis) slots out xs actual
  have tape : (fun i => xs (slots i)) = Fin.cons K p := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i
  rw [tape] at decoded
  apply liftMember codAxis K d (auxiliaryTerm d c f a) out p domIn decoded
  intro β j Δ block keep report
  rw [auxiliaryRename]
  have cod := renameInto codIn j Δ keep
  have fn := renameInto fnIn j Δ keep
  have arg := renameInto argIn j Δ keep
  simp only [graphRename] at cod fn arg
  have same : (Fin.cons (d.relabel j) (fun i => (p i).relabel j) : Fin 3 → OTerm β) =
      ![d.relabel j,K.relabel j,T.relabel j] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i
  rw [same] at report
  exact fromCodAxis (K.relabel j) (T.relabel j) (d.relabel j) (c.relabel j) (f.relabel j) (a.relabel j) block cod fn arg report

#print axioms exact_OpenAuxApplicationsMember

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsThinOpenProof
