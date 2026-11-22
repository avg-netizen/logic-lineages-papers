module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsConstructorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsOriginProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinderTransportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTransportProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialElimination)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn bindEmbedding liftBind varBind z)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open ID1Completion.InternalBinderTransportProof (actualUniversalRenaming)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open SourceComputabilityFormulaSupportProof (allOne)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalCoverArgumentCellsTargets
open NumberedWindowInternalCoverArgumentCellsConstructorProof (sentinel paired)
open NumberedWindowInternalCoverArgumentCellsOriginProof (exact_OpenCoverArgumentCellsOrigin)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem impRename {β : Type} (P Q : Formula α) (j : α → β) :
    (P.imp Q).relabel j = (P.relabel j).imp (Q.relabel j) := rfl

theorem axisRename {β : Type} (old next : OTerm α) (j : α → β) :
    (axisInclusion old next).relabel j = axisInclusion (old.relabel j) (next.relabel j) := by
  simp only [axisInclusion,actualUniversalRenaming,impRename,graphRename,Term.relabel_relabel] <;> rfl

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

private theorem transportPair (next ts ts' ars ars' key : OTerm α)
    (large : Nonempty (Derivation body Γ (cellsReport next ts' ars')))
    (ht : Nonempty (Derivation body Γ (axisInclusion ts ts')))
    (ha : Nonempty (Derivation body Γ (axisInclusion ars ars')))
    (old : Nonempty (Derivation body Γ (cellPairOrigin ts ars key))) :
    Nonempty (Derivation body Γ (memberGraph next key)) := by
  let clause := cellOriginMatrix ts ars key
  let j : α → α ⊕ Fin 2 := Sum.inl
  let Δ := clause :: Γ.map (fun q => q.relabel j)
  let q : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let a : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  apply actualFiniteExistentialElimination body α 2 Γ clause (memberGraph next key) old
  rw [graphRename]
  have keep : ∀ r ∈ Γ, r.relabel j ∈ Δ := by
    intro r h
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r,h,rfl⟩)
  have htr := renameInto ht j Δ keep
  have har := renameInto ha j Δ keep
  have actual := renameInto large j Δ keep
  rw [axisRename] at htr har
  simp only [cellsReport,programRename,binaryInputsRename] at actual
  have row : Derivation body Δ (cellOriginRow (ts.relabel j) (ars.relabel j) (key.relabel j) q a) :=
    Derivation.hypothesis List.mem_cons_self
  have rest := Derivation.conjunctionRight row
  have qHit := useAxis (ts.relabel j) (ts'.relabel j) q htr (Derivation.conjunctionLeft row)
  have aHit := useAxis (ars.relabel j) (ars'.relabel j) a har (Derivation.conjunctionLeft rest)
  obtain ⟨found⟩ := paired (next.relabel j) (ts'.relabel j) (ars'.relabel j) q a actual qHit aHit
  exact transportKey (next.relabel j) (rawCons q a) (key.relabel j) (Derivation.conjunctionRight rest) found

theorem exact_OpenCoverArgumentCellsTransport : ExactOpenCoverArgumentCellsTransport := by
  intro body α Γ out next ts ts' ars ars' key old large ht ha hit
  obtain ⟨origin⟩ := exact_OpenCoverArgumentCellsOrigin body α Γ out ts ars key old hit
  let H := eqn z key
  let P := cellPairOrigin ts ars key
  obtain ⟨atZero⟩ := sentinel (body := body) (Γ := H :: Γ) next ts' ars' (withHyp large H)
  obtain ⟨first⟩ := transportKey (Γ := H :: Γ) next z key
    (Derivation.hypothesis List.mem_cons_self) atZero
  obtain ⟨second⟩ := transportPair (Γ := P :: Γ) next ts ts' ars ars' key
    (withHyp large P) (withHyp ht P) (withHyp ha P) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination origin (Derivation.implicationIntroduction first)
    (Derivation.implicationIntroduction second)⟩

#print axioms exact_OpenCoverArgumentCellsTransport

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTransportProof
