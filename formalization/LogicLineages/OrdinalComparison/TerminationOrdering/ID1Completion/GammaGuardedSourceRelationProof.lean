module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceRelationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open GammaGuardedSource GammaGuardedSourceSyntaxProof GammaGuardedSourceCertificateProof
open GuardedSourceGraphSupportProof GuardedSourceSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem relationTransport (oldSource : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (valid gamma : Program 1) (tag : Program 2) (window : Program 1)
    (context : Nat) (typ x y u : OTerm α)
    (ht : Nonempty (Derivation body Gamma
      (GuardedSource.literalTyped (computability oldComp valid gamma tag) context typ x)))
    (hr : Nonempty (Derivation body Gamma
      (GuardedSource.literalR (source oldSource oldComp.typed valid gamma tag window) context x y)))
    (hg : Nonempty (Derivation body Gamma
      (literalGuard (computability oldComp valid gamma tag) y u))) :
    Nonempty (Derivation body Gamma (literalGuard (computability oldComp valid gamma tag) x u)) := by
  rw [literalTypedGraph] at ht
  rw [literalGuardGraph] at hg ⊢
  rw [literalRGraph] at hr
  obtain ⟨dr⟩ := hr
  let P : Formula (α ⊕ Fin 1) := programGraph
    (GuardedSource.guardedPositive (basePositive oldSource.positive gamma)
      (baseTyped oldComp.typed valid) tag window) (suc z)
    ![numeral context,x.relabel Sum.inl,y.relabel Sum.inl,.var (.inr 0)]
  let Delta := P :: Gamma.map weaken
  have ht' := renameInto ht Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  have hg' := renameInto hg Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  simp only [programRename,sucRelabel,zRelabel,tupleTwoRename,tupleThreeRename,numeralRename] at ht' hg'
  have h := certificateTransport oldComp.typed oldSource.positive valid gamma tag window
    (numeral context) (typ.relabel Sum.inl) (x.relabel Sum.inl) (y.relabel Sum.inl)
    (u.relabel Sum.inl) (.var (.inr 0)) ht'
    (show Nonempty (Derivation body Delta P) from ⟨Derivation.hypothesis List.mem_cons_self⟩) hg'
  have hd : Nonempty (Derivation body Delta (weaken
      (programGraph (computability oldComp valid gamma tag).guard (suc z) ![x,u]))) := by
    simpa only [computability,baseComputability,GuardedSource.computability,weaken,
      programRename,sucRelabel,zRelabel,tupleTwoRename] using h
  obtain ⟨dd⟩ := hd
  exact ⟨Derivation.existentialElimination dr dd⟩

theorem actualOriginalGuardTransport : GammaGuardedSourceTargets.ActualOriginalGuardTransport := by
  intro oldSource oldComp valid gamma tag window context α typ x y u
  let src := source oldSource oldComp.typed valid gamma tag window
  let comp := computability oldComp valid gamma tag
  let P := ((GuardedSource.literalTyped comp context typ x ⊓ GuardedSource.literalR src context x y) ⊓
    literalGuard comp y u)
  have h : Derivation (SourcePresentation.sourceBody src context) [P] P :=
    Derivation.hypothesis List.mem_cons_self
  obtain ⟨d⟩ := relationTransport oldSource oldComp valid gamma tag window context typ x y u
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionLeft h)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionLeft h)⟩
    ⟨Derivation.conjunctionRight h⟩
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceRelationProof
