module

public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalFirstHopAddressProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAddressAtKnownFoldProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginalOneHopInversionProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename outputTransport equalEqn)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalOriginalFirstHopCoreProof (D oneHopProgram)
open NumberedWindowInternalOriginalFirstHopAddressProof (R hop)
open NumberedWindowInternalOriginalFirstHopTailProof (exact_PositiveHeadNilEndpoint)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePairChecks (exact_OpenFieldConsInjective)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparsePositiveFold (positive)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt headData)
open NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof (headCases)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (someHopCalls)
open NumberedWindowInternalSparsePathSuccessfulAdvanceSyntaxProof (reportRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceChecks (exact_OpenSuccessfulAdvanceCalls)
open NumberedWindowInternalParameterizedAddressPositive (addressAt exact_OriginalAddressAt)
open NumberedWindowInternalAddressAtKnownFoldProof (exact_OpenAddressAtKnownFold)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OneHopProgramElim (P : Program 3) (x hd y : OTerm α)
    (held : D B Γ (programGraph (oneHopProgram P) (suc z) ![x,hd,y])) :
    D B Γ (programGraph P (suc z) ![x,rawCons hd z,y]) := by
  let xs : Fin 3 → OTerm α := ![x,hd,y]
  have cell : D B Γ (programGraph (.composition fieldCons ![.projection 1,constantZero 3])
      (rawCons hd z) xs) := by
    apply compositionValue fieldCons ![.projection 1,constantZero 3] (rawCons hd z) xs ![hd,z]
      (NumberedWindowInternalSparsePairGraphProof.consGraph hd z)
    intro k
    exact Fin.cases (projectionValue 1 xs)
      (Fin.cases (constantZeroValue xs) (fun q => Fin.elim0 q)) k
  apply compositionRecover P ![.projection 0,.composition fieldCons ![.projection 1,constantZero 3],
    .projection 2] (suc z) xs ![x,rawCons hd z,y] held
  intro k
  exact Fin.cases (projectionValue 0 xs)
    (Fin.cases cell (Fin.cases (projectionValue 2 xs) (fun q => Fin.elim0 q))) k

private theorem hopTransport (raw : Program 5) (least : Program 3)
    (out ctx ty current hd old : OTerm α) (eq : D B Γ (eqn hd old))
    (held : D B Γ (selectedGraph raw least out ctx ty current hd)) :
    D B Γ (selectedGraph raw least out ctx ty current old) := by
  unfold selectedGraph programGraph at held ⊢
  apply graphInputTransport B α 4 Γ (OrdinaryArithmetic.graphFormula (advance raw least)) out
    ![ctx,ty,current,hd] ![ctx,ty,current,old] _ held
  intro a
  refine Fin.cases ?_ (fun b => Fin.cases ?_ (fun d => Fin.cases ?_ (fun e => Fin.cases ?_
    (fun q => Fin.elim0 q) e) d) b) a
  · change D B Γ (equal ctx ctx); rw [equalEqn]; exact ⟨refl ctx⟩
  · change D B Γ (equal ty ty); rw [equalEqn]; exact ⟨refl ty⟩
  · change D B Γ (equal current current); rw [equalEqn]; exact ⟨refl current⟩
  · change D B Γ (equal hd old); rw [equalEqn]; exact eq

/-- One actual accepted direct hop, with its original address reports,
exposes precisely the existing certified raw callback and both least
calls. The hop or its endpoint is not replaced by a chosen proxy. -/
theorem exact_OneHopRawInversionAtReports (cv tv : Program 1)
    (raw : Program 5) (least : Program 3) (x cert y ctx ty src dst : OTerm α)
    (left : D B Γ (addressReport x ctx ty src)) (right : D B Γ (addressReport y ctx ty dst))
    (held : D B Γ (programGraph (hop cv tv raw least) (suc z) ![x,cert,y])) :
    D B Γ (someHopCalls raw least ctx ty src cert dst) := by
  have whole := exact_OneHopProgramElim (R cv tv raw least) x cert y held
  have actual : D B Γ (programGraph (addressAt cv tv (positive raw least)) (suc z) ![x,rawCons cert z,y]) := by
    rw [exact_OriginalAddressAt]
    exact whole
  have decodedFold := exact_OpenAddressAtKnownFold cv tv (positive raw least) x (rawCons cert z) y
    ctx ty src dst left right actual
  have unfolded := NumberedWindowInternalSparsePositiveHeadDecompositionForwardProof.forward raw least
    ctx ty src (rawCons cert z) dst decodedFold
  apply headCases raw least ctx ty src (rawCons cert z) dst _ unfolded
  intro β j Δ head tail mid _ fields
  rw [reportRename]
  let c := ctx.relabel j
  let t := ty.relabel j
  let s := src.relabel j
  let d := dst.relabel j
  let w := cert.relabel j
  obtain ⟨facts⟩ := fields
  have cell := Derivation.conjunctionLeft facts
  rw [rawConsRename,zRelabel] at cell
  obtain ⟨actual⟩ := NumberedWindowInternalSparsePairGraphProof.consGraph (body := B) (Γ := Δ) w z
  obtain ⟨rule⟩ := exact_OpenFieldConsInjective B β (rawCons w z) head tail w z
  obtain ⟨eqs⟩ := closedApply ⟨rule⟩ ⟨Derivation.conjunctionIntroduction cell actual⟩
  rw [equalEqn,equalEqn] at eqs
  have rest := Derivation.conjunctionRight facts
  have ends := exact_PositiveHeadNilEndpoint raw least c t mid tail d
    ⟨Derivation.conjunctionRight rest⟩ ⟨Derivation.conjunctionRight eqs⟩
  have midAt := hopTransport raw least (suc mid) c t (suc s) head w
    ⟨Derivation.conjunctionLeft eqs⟩ ⟨Derivation.conjunctionLeft rest⟩
  have step := outputTransport (advance raw least) (suc mid) (suc d) ![c,t,suc s,w] ends midAt
  obtain ⟨both⟩ := exact_OpenSuccessfulAdvanceCalls B raw least β c t s w d
  exact closedApply ⟨Derivation.conjunctionLeft both⟩ step

#print axioms exact_OneHopProgramElim
#print axioms exact_OneHopRawInversionAtReports
end LogicLineages.PersistentMarking.NumberedWindowInternalOriginalOneHopInversionProof
