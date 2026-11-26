module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptInductionSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptTailTransferProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptNilProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptInductionProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalListInduction (atCode atIndex constructors constructorBody premises)
open ID1Completion.InternalListInductionProof (actualOriginalListInductionAtCode)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction actualFiniteUniversalElimination)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucRelabel zRelabel)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalOriginKeptSplitTargets (splitExists)
open NumberedWindowInternalOriginKeptInductionSyntaxProof
open NumberedWindowInternalOriginKeptNilProof (exact_OriginalKeptSplitNil)
open NumberedWindowInternalOriginKeptTailTransferProof (exact_OriginalKeptTailTransfer)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)

attribute [local irreducible] programGraph

/-- The one unpaid local allocation in the inductive part: after the
head was moved to the extra removed tape, assign it to one side
using an exact one-occurrence erase. No whole allocation assumed. -/
def MoveOneKeptSupply (B : Positive (Fin 1)) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (l r kept head tail removed extra : OTerm α),
    Nonempty (Derivation B Γ (consGraph kept head tail)) →
    Nonempty (Derivation B Γ (consGraph extra head removed)) →
    Nonempty (Derivation B Γ (splitExists l r tail extra)) →
    Nonempty (Derivation B Γ (splitExists l r kept removed))

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem applyAt (l r k src d dst : OTerm α)
    (h : Nonempty (Derivation B Γ (invariantAt l r k src)))
    (a : Nonempty (Derivation B Γ (A k d dst)))
    (c : Nonempty (Derivation B Γ (C src dst))) :
    Nonempty (Derivation B Γ (splitExists l r k d)) := by
  obtain ⟨p⟩ := actualFiniteUniversalElimination B α 2 Γ (invariantMatrix l r k src)
    (fun i => emb (![d,dst] i)) h
  rw [invariantWitness] at p
  obtain ⟨pA⟩ := a
  obtain ⟨pC⟩ := c
  exact ⟨Derivation.implicationElimination p (Derivation.conjunctionIntroduction pA pC)⟩

private theorem introAt (l r k src : OTerm α)
    (prove : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (d dst : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (A (k.relabel j) d dst)) →
      Nonempty (Derivation B Δ (C (src.relabel j) dst)) →
      Nonempty (Derivation B Δ (splitExists (l.relabel j) (r.relabel j) (k.relabel j) d))) :
    Nonempty (Derivation B Γ (invariantAt l r k src)) := by
  apply actualFiniteUniversalIntroduction B α 2 Γ (invariantMatrix l r k src)
  let j : α → α ⊕ Fin 2 := Sum.inl
  let D : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let W : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  let H := A (k.relabel j) D W ⊓ C (src.relabel j) W
  let Δ := H :: Γ.map (fun q => q.relabel j)
  have own : Derivation B Δ H := Derivation.hypothesis List.mem_cons_self
  obtain ⟨paid⟩ := prove (α ⊕ Fin 2) j Δ D W
    (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
    ⟨Derivation.conjunctionLeft own⟩ ⟨Derivation.conjunctionRight own⟩
  exact ⟨Derivation.implicationIntroduction paid⟩

private theorem nilAt (l r src : OTerm α) (hold : Nonempty (Derivation B Γ (A l r src))) :
    Nonempty (Derivation B Γ (invariantAt l r z src)) := by
  apply introAt l r z src
  intro β j Δ d dst keep a c
  rw [zRelabel] at a ⊢
  exact exact_OriginalKeptSplitNil (l.relabel j) (r.relabel j) d (src.relabel j) dst
    (renamePair append src l r hold j keep) a c

private theorem consAt (pay : MoveOneKeptSupply B) (l r k h t src : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph k h t)))
    (ih : Nonempty (Derivation B Γ (invariantAt l r t src))) :
    Nonempty (Derivation B Γ (invariantAt l r k src)) := by
  apply introAt l r k src
  intro β j Δ d dst keep a c
  have cc := renameInto cell j Δ keep
  rw [consGraphRename] at cc
  have ii := renameInto ih j Δ keep
  rw [invariantRename] at ii
  apply exact_OriginalKeptTailTransfer (src.relabel j) (k.relabel j) (h.relabel j)
    (t.relabel j) d dst cc a c _
  intro γ ρ Ω extra out holds e pa ba
  rw [splitRename]
  have jh := renameInto cc ρ Ω holds
  rw [consGraphRename] at jh
  have ih' := renameInto ii ρ Ω holds
  rw [invariantRename] at ih'
  have prev := applyAt ((l.relabel j).relabel ρ) ((r.relabel j).relabel ρ)
    ((t.relabel j).relabel ρ) ((src.relabel j).relabel ρ) extra out ih' pa ba
  exact pay γ Ω ((l.relabel j).relabel ρ) ((r.relabel j).relabel ρ)
    ((k.relabel j).relabel ρ) ((h.relabel j).relabel ρ) ((t.relabel j).relabel ρ)
    (d.relabel ρ) extra jh e prev

private theorem constructorLaw (pay : MoveOneKeptSupply B) (l r src : OTerm α) :
    Nonempty (Derivation B Γ (constructors (motive l r src))) := by
  apply actualFiniteUniversalIntroduction B α 3 Γ (constructorBody (motive l r src))
  let j : α → α ⊕ Fin 3 := Sum.inl
  let K : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let H : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let T : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let C₀ := consGraph K H T
  let I := invariantAt (l.relabel j) (r.relabel j) T (src.relabel j)
  let Δ := I :: C₀ :: Γ.map (fun q => q.relabel j)
  change Nonempty (Derivation B (Γ.map (fun q => q.relabel j))
    (C₀.imp ((atIndex (motive l r src) 2).imp (atIndex (motive l r src) 0))))
  simp only [motiveIndex]
  obtain ⟨d⟩ := consAt (Γ := Δ) pay (l.relabel j) (r.relabel j) K H T (src.relabel j)
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩

/-- Native arbitrary symbolic kept-tape induction. The actual local
one-occurrence side move is still explicit; all symbolic iteration,
count balance under moving the head, and witness packing are paid. -/
theorem exact_OriginalKeptSplitInduction (pay : MoveOneKeptSupply B)
    (l r k d src dst : OTerm α)
    (srcRead : Nonempty (Derivation B Γ (A l r src)))
    (dstRead : Nonempty (Derivation B Γ (A k d dst)))
    (bal : Nonempty (Derivation B Γ (C src dst))) :
    Nonempty (Derivation B Γ (splitExists l r k d)) := by
  have base : Nonempty (Derivation B Γ (atCode (motive l r src) z)) := by
    rw [motiveCode]
    exact nilAt l r src srcRead
  obtain ⟨b⟩ := base
  obtain ⟨s⟩ := constructorLaw (Γ := Γ) pay l r src
  have prep : Nonempty (Derivation B Γ (premises (motive l r src))) :=
    ⟨Derivation.conjunctionIntroduction b s⟩
  have all := actualOriginalListInductionAtCode B α Γ (motive l r src) k prep
  rw [motiveCode] at all
  exact applyAt l r k src d dst all dstRead bal

#print axioms exact_OriginalKeptSplitInduction
end LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptInductionProof
