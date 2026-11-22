module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerConstructorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerOriginProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerTransportProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialElimination)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn bindEmbedding liftBind varBind z)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalCoverNumberedLayerTargets
open NumberedWindowInternalCoverNumberedLayerConstructorProof (exact_OpenCoverNumberedLayerConstructor)
open NumberedWindowInternalCoverNumberedLayerOriginProof (exact_OpenCoverNumberedLayerOrigin)
open NumberedWindowInternalCoverArgumentCellsTargets (axisInclusion)
open NumberedWindowInternalCoverArgumentCellsTransportProof (axisRename)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem useAxis (old next key : OTerm α)
    (inclusion : Nonempty (Derivation body Γ (axisInclusion old next)))
    (oldKey : Derivation body Γ (memberGraph old key)) :
    Nonempty (Derivation body Γ (memberGraph next key)) := by
  obtain ⟨all⟩ := inclusion
  have selected := Derivation.universalElimination (emb key) all
  have step : Derivation body Γ ((memberGraph old key).imp (memberGraph next key)) := by
    simpa only [instantiate,bindEmbedding,impSubst,memberSubst,liftBind,varBind] using selected
  exact ⟨Derivation.implicationElimination step oldKey⟩

private theorem transportKey (out a key : OTerm α)
    (eq : Derivation body Γ (eqn a key))
    (hit : Derivation body Γ (memberGraph out a)) :
    Nonempty (Derivation body Γ (memberGraph out key)) := by
  let clause : Formula (α ⊕ Fin 1) := memberGraph (out.relabel Sum.inl) (.var (.inr 0))
  have inst (w : OTerm α) : instantiate clause (emb w) = memberGraph out w := by
    simp only [clause,instantiate,bindEmbedding,memberSubst,liftBind,varBind]
  exact ⟨(inst key) ▸ Derivation.equalityElimination clause (emb a) (emb key) eq ((inst a).symm ▸ hit)⟩

theorem exact_OpenCoverNumberedLayerTransport : ExactOpenCoverNumberedLayerTransport := by
  intro body α Γ old next H K ids ids' args args' key small large incIds incArgs hit
  have origin := exact_OpenCoverNumberedLayerOrigin body α Γ old H K ids args key small hit
  let clause := numberedOriginMatrix H K ids args key
  let j : α → α ⊕ Fin 5 := Sum.inl
  let Δ := clause :: Γ.map (fun q => q.relabel j)
  let h : OTerm (α ⊕ Fin 5) := .var (.inr 0)
  let ty : OTerm (α ⊕ Fin 5) := .var (.inr 1)
  let k : OTerm (α ⊕ Fin 5) := .var (.inr 2)
  let l : OTerm (α ⊕ Fin 5) := .var (.inr 3)
  let r : OTerm (α ⊕ Fin 5) := .var (.inr 4)
  apply actualFiniteExistentialElimination body α 5 Γ clause (memberGraph next key) origin
  rw [graphRename]
  have keep : ∀ p ∈ Γ, p.relabel j ∈ Δ := by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have actual := renameInto large j Δ keep
  simp only [numberedReport,programRename,quadInputsRename] at actual
  have moreIds := renameInto incIds j Δ keep
  have moreArgs := renameInto incArgs j Δ keep
  rw [axisRename] at moreIds moreArgs
  have row : Derivation body Δ
      (numberedOriginRow (H.relabel j) (K.relabel j) (ids.relabel j) (args.relabel j) (key.relabel j)
        h ty k l r) := Derivation.hypothesis List.mem_cons_self
  have rest1 := Derivation.conjunctionRight row
  have rest2 := Derivation.conjunctionRight rest1
  have rest3 := Derivation.conjunctionRight rest2
  have rest4 := Derivation.conjunctionRight rest3
  have newId := useAxis (ids.relabel j) (ids'.relabel j) k moreIds (Derivation.conjunctionLeft rest2)
  have newLeft := useAxis (args.relabel j) (args'.relabel j) l moreArgs (Derivation.conjunctionLeft rest3)
  have newRight := useAxis (args.relabel j) (args'.relabel j) r moreArgs (Derivation.conjunctionLeft rest4)
  obtain ⟨found⟩ := exact_OpenCoverNumberedLayerConstructor body (α ⊕ Fin 5) Δ
    (next.relabel j) (H.relabel j) (K.relabel j) (ids'.relabel j) (args'.relabel j) h ty k l r actual
    ⟨Derivation.conjunctionLeft row⟩ ⟨Derivation.conjunctionLeft rest1⟩ newId newLeft newRight
  exact transportKey (next.relabel j) (numberedTerm h ty k l r) (key.relabel j)
    (Derivation.conjunctionRight rest4) found

#print axioms exact_OpenCoverNumberedLayerTransport

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerTransportProof
