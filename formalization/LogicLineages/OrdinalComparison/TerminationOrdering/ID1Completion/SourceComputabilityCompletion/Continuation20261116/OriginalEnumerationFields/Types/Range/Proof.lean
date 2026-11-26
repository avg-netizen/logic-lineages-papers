module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.Range.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.Range.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalGraphCompositionFunctionalityProof
open Continuation20261114.HeadWindowBooleanRange
open SyntaxProof BindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem step (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (AtRaw raw)) := by
  apply atRawIntro raw
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let allowed : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
  let out : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
  let G := graph2 allTypes out (raw.relabel Sum.inl) allowed
  let Theta := G :: Delta.map (fun q => q.relabel Sum.inl)
  have ihj := renameInto ih (Sum.inl : alpha → alpha ⊕ Fin 2) Theta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [belowRawRename] at ihj
  exact Classical.choice (CoreProof.core (raw.relabel Sum.inl) allowed out ihj
    (show Nonempty (Derivation body Theta G) from ⟨Derivation.hypothesis List.mem_cons_self⟩))

theorem allTypesRange : ProgramRangeProof.Ranged allTypes := by
  intro body alpha Delta out xs hg
  have hx : xs = Fin.cons (xs 0) (Fin.cons (xs 1) Fin.elim0) := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hg
  exact atRawApply (xs 0) (xs 1) out (rawInduction (xs 0) (fun _ _ r ih => step r ih)) hg
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.Range.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.Range.Proof
