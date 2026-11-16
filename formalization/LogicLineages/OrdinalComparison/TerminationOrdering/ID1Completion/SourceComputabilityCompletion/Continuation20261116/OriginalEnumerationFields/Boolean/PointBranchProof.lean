module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.PointBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.PointBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalAcceptanceBranchProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open Continuation20261114.HeadWindowBooleanRange
open Continuation20261114.HeadWindowBooleanRange.InductionSyntaxProof (booleanRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open PointRange PointSyntaxProof PointBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)} {k : Nat}
attribute [local irreducible] programGraph

theorem branchOutput (c a b : Program k) (xs : Fin k → OTerm alpha) (out : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (At a xs)))
    (hb : Nonempty (Derivation body Delta (At b xs)))
    (hw : Nonempty (Derivation body Delta (programGraph (InternalAcceptance.branch c a b) out xs))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  apply programCases c xs _
  intro beta j Theta value hj hc
  rw [booleanRename]
  have haj := renameInto ha j Theta hj
  have hbj := renameInto hb j Theta hj
  rw [atRename] at haj hbj
  have hwj := renameInto hw j Theta hj
  rw [programRename] at hwj
  apply zeroSuccessorCases Theta value _
  · have hz : Nonempty (Derivation body (eqn value z :: Theta) (eqn value z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hcz := outputTransport c value z (fun i => (xs i).relabel j) hz (withHyp hc (eqn value z))
    exact applyAt a (fun i => (xs i).relabel j) (out.relabel j) (withHyp haj (eqn value z))
      (zeroBranchElim c a b (out.relabel j) _ hcz (withHyp hwj (eqn value z)))
  · intro gamma l Xi pred hl he
    rw [booleanRename]
    have hcl := renameInto hc l Xi hl
    have hwl := renameInto hwj l Xi hl
    have hbl := renameInto hbj l Xi hl
    rw [atRename] at hbl
    simp only [programRename] at hcl hwl
    have hcs := outputTransport c (value.relabel l) (suc pred)
      (fun i => ((xs i).relabel j).relabel l) he hcl
    exact applyAt b (fun i => ((xs i).relabel j).relabel l) ((out.relabel j).relabel l) hbl
      (successorBranchElim c a b ((out.relabel j).relabel l) pred _ hcs hwl)

theorem branchAt (c a b : Program k) (xs : Fin k → OTerm alpha)
    (ha : Nonempty (Derivation body Delta (At a xs)))
    (hb : Nonempty (Derivation body Delta (At b xs))) :
    Nonempty (Derivation body Delta (At (InternalAcceptance.branch c a b) xs)) := by
  apply introAt (InternalAcceptance.branch c a b) xs
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let Theta : List (Formula (alpha ⊕ Fin 1)) :=
    programGraph (InternalAcceptance.branch c a b) (.var (.inr 0)) (fun i => (xs i).relabel Sum.inl) ::
      Delta.map (fun q => q.relabel Sum.inl)
  have hj : ∀ q ∈ Delta, q.relabel (Sum.inl : alpha → alpha ⊕ Fin 1) ∈ Theta := by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have haj := renameInto ha (Sum.inl : alpha → alpha ⊕ Fin 1) Theta hj
  have hbj := renameInto hb (Sum.inl : alpha → alpha ⊕ Fin 1) Theta hj
  rw [atRename] at haj hbj
  exact Classical.choice (branchOutput c a b (fun i => (xs i).relabel Sum.inl) (.var (.inr 0)) haj hbj
    ⟨Derivation.hypothesis List.mem_cons_self⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.PointBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.PointBranchProof
