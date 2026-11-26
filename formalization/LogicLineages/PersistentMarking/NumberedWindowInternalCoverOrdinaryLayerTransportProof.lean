module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerConstructorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerOriginProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerTransportProof
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
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalCoverOrdinaryLayerTargets
open NumberedWindowInternalCoverOrdinaryLayerConstructorProof (openTaggedLayerConstructor)
open NumberedWindowInternalCoverOrdinaryLayerOriginProof (openTaggedLayerOrigin)
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

theorem openTaggedLayerTransport (tag : Nat) : ExactOpenTaggedLayerTransport tag := by
  intro body α Γ old next K children children' key small large inc hit
  have origin := openTaggedLayerOrigin tag body α Γ old K children key small hit
  let clause := taggedOriginMatrix tag K children key
  let j : α → α ⊕ Fin 2 := Sum.inl
  let Δ := clause :: Γ.map (fun q => q.relabel j)
  let ty : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let q : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  apply actualFiniteExistentialElimination body α 2 Γ clause (memberGraph next key) origin
  rw [graphRename]
  have keep : ∀ r ∈ Γ, r.relabel j ∈ Δ := by
    intro r h
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r,h,rfl⟩)
  have actual := renameInto large j Δ keep
  simp only [taggedReport,programRename,binaryInputsRename] at actual
  have larger := renameInto inc j Δ keep
  rw [axisRename] at larger
  have row : Derivation body Δ (taggedOriginRow tag (K.relabel j) (children.relabel j) (key.relabel j) ty q) :=
    Derivation.hypothesis List.mem_cons_self
  have rest := Derivation.conjunctionRight row
  have qHit := useAxis (children.relabel j) (children'.relabel j) q larger (Derivation.conjunctionLeft rest)
  obtain ⟨found⟩ := openTaggedLayerConstructor tag body (α ⊕ Fin 2) Δ
    (next.relabel j) (K.relabel j) (children'.relabel j) ty q actual ⟨Derivation.conjunctionLeft row⟩ qHit
  exact transportKey (next.relabel j) (taggedTerm tag ty q) (key.relabel j) (Derivation.conjunctionRight rest) found

theorem exact_OpenCoverOrdinaryLayerTransport : ExactOpenCoverOrdinaryLayerTransport :=
  openTaggedLayerTransport 4

#print axioms exact_OpenCoverOrdinaryLayerTransport

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerTransportProof
