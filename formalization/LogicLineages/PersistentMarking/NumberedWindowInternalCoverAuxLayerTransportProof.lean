module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLayerTransportTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsThinOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLayerOriginProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLayerTransportProof
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
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverAuxLayerTransportTargets
open NumberedWindowInternalCoverAuxApplicationsThinOpenProof (exact_OpenAuxApplicationsMember)
open NumberedWindowInternalCoverAuxLayerOriginProof (exact_OpenCoverAuxLayerOrigin)
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

theorem exact_OpenCoverAuxLayerTransport : ExactOpenCoverAuxLayerTransport := by
  intro body α Γ old next K T T' key small large inc hit
  have origin := exact_OpenCoverAuxLayerOrigin body α Γ old K T key small hit
  let clause := auxOriginMatrix K T key
  let j : α → α ⊕ Fin 4 := Sum.inl
  let Δ := clause :: Γ.map (fun q => q.relabel j)
  let d : OTerm (α ⊕ Fin 4) := .var (.inr 0)
  let c : OTerm (α ⊕ Fin 4) := .var (.inr 1)
  let f : OTerm (α ⊕ Fin 4) := .var (.inr 2)
  let a : OTerm (α ⊕ Fin 4) := .var (.inr 3)
  apply actualFiniteExistentialElimination body α 4 Γ clause (memberGraph next key) origin
  rw [graphRename]
  have keep : ∀ p ∈ Γ, p.relabel j ∈ Δ := by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have actual := renameInto large j Δ keep
  simp only [auxReport,programRename,binaryInputsRename] at actual
  have more := renameInto inc j Δ keep
  rw [axisRename] at more
  have row : Derivation body Δ (auxOriginRow (K.relabel j) (T.relabel j)
      (key.relabel j) d c f a) := Derivation.hypothesis List.mem_cons_self
  have rest1 := Derivation.conjunctionRight row
  have rest2 := Derivation.conjunctionRight rest1
  have rest3 := Derivation.conjunctionRight rest2
  have newFun := useAxis (T.relabel j) (T'.relabel j) f more (Derivation.conjunctionLeft rest2)
  have newArg := useAxis (T.relabel j) (T'.relabel j) a more (Derivation.conjunctionLeft rest3)
  obtain ⟨found⟩ := exact_OpenAuxApplicationsMember body (α ⊕ Fin 4) Δ
    (K.relabel j) (T'.relabel j) d c f a (next.relabel j) ⟨Derivation.conjunctionLeft row⟩
    ⟨Derivation.conjunctionLeft rest1⟩ newFun newArg actual
  exact transportKey (next.relabel j) (auxiliaryTerm d c f a) (key.relabel j)
    (Derivation.conjunctionRight rest3) found

#print axioms exact_OpenCoverAuxLayerTransport

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLayerTransportProof
