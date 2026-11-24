module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseParsedFoldSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseParsedFoldProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalStrongInduction ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalStrongInductionProof (strongInduction)
open ID1Completion.InternalStrongInductionSyntaxProof (belowRename belowElimSyntax)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons z suc)
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldCellTargets (certifiedCell)
open NumberedWindowInternalCertifiedUnionProgressSupportProof (Preserves freshKeeps keepsComp)
open NumberedWindowInternalConsUnionReportBuildProof (Report)
open NumberedWindowInternalSparseParserPositiveCasesProof (exact_OriginalPositiveSparseParserCases)
open NumberedWindowInternalSparseParsedFoldSyntaxProof

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem eliminateParsedMotive {β : Type} (theta : Formula (α ⊕ Fin 2))
    (r : α → OTerm β) (n s : OTerm β) (Δ : List (Formula β))
    (held : Nonempty (Derivation B Δ (parsedAt theta r n)))
    (seen : Report (B := B) (Γ := Δ) parser (suc s) ![n]) :
    Nonempty (Derivation B Δ (pairAt theta r n s)) := by
  obtain ⟨h⟩ := held
  obtain ⟨seen⟩ := seen
  have hi : Derivation B Δ (instantiate (parsedMatrix theta r n) (emb s)) :=
    Derivation.universalElimination (emb s) h
  rw [parsedMatrixAt] at hi
  exact ⟨Derivation.implicationElimination hi seen⟩

/-- True local cases for a formula on the raw code and its observed scratch.
A cons case receives a proof of that exact formula at its true smaller
raw tail and actual observed scratch suffix, not a semantic assertion. -/
structure ParsedFoldCases (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (theta : Formula (α ⊕ Fin 2)) : Prop where
  nilCase : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (n s : OTerm β),
    Preserves Γ j Δ →
    Nonempty (Derivation B Δ (eqn n z)) →
    Nonempty (Derivation B Δ (eqn s z)) →
    Nonempty (Derivation B Δ (pairAt theta (fun i => .var (j i)) n s))
  consCase : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (n s h t st : OTerm β),
    Preserves Γ j Δ →
    Nonempty (Derivation B Δ (certifiedCell n h t)) →
    Nonempty (Derivation B Δ (consGraph n h t)) →
    Nonempty (Derivation B Δ (eqn n (rawCons h t))) →
    Nonempty (Derivation B Δ (ltF t n)) →
    Report (B := B) (Γ := Δ) parser (suc st) ![t] →
    Report (B := B) (Γ := Δ) consCode s ![h,st] →
    Nonempty (Derivation B Δ (pairAt theta (fun i => .var (j i)) t st)) →
    Nonempty (Derivation B Δ (pairAt theta (fun i => .var (j i)) n s))

/-- For every actual original positive parsed code, derive the supplied
object formula. The induction is the same original ordered course-of-values
rule used by #621, with the actual positive parser premise in the motive. -/
theorem exact_OriginalSparseParsedFoldAll (theta : Formula (α ⊕ Fin 2))
    (cases : ParsedFoldCases B Γ theta) :
    Nonempty (Derivation B Γ (allOne (foldMotive theta))) := by
  apply strongInduction (foldMotive theta)
  let n : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let lower := below (lift (foldMotive theta)) n
  let Γ₁ := lower :: Γ.map weaken
  let n₂ : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := n.relabel Sum.inl
  let s : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
  let seen := positiveGraph n₂ s
  let Γ₂ := seen :: Γ₁.map weaken
  let j₁ : α → α ⊕ Fin 1 := Sum.inl
  let j₂ : (α ⊕ Fin 1) → (α ⊕ Fin 1) ⊕ Fin 1 := Sum.inl
  let r : α → OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := fun i => .var (j₂ (j₁ i))
  have baseKeeps : Preserves Γ₁ j₂ Γ₂ := freshKeeps Γ₁ seen
  have paramKeeps : Preserves Γ (j₂ ∘ j₁) Γ₂ :=
    keepsComp Γ Γ₁ Γ₂ j₁ j₂ (freshKeeps Γ lower) baseKeeps
  have hBelow : Nonempty (Derivation B Γ₁ lower) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hSeen : Report (B := B) (Γ := Γ₂) parser (suc s) ![n₂] :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have progress : Nonempty (Derivation B Γ₂ (pairAt theta r n₂ s)) := by
    apply exact_OriginalPositiveSparseParserCases n₂ s (pairAt theta r n₂ s) hSeen
    · intro sZero
      exact cases.nilCase _ (j₂ ∘ j₁) (eqn n₂ z :: Γ₂) n₂ s
        (fun p hp => List.mem_cons_of_mem _ (paramKeeps p hp))
        ⟨Derivation.hypothesis List.mem_cons_self⟩ sZero
    · intro β k Δ h t st keep cell shape eqRaw strict tail scratch
      let join : (α ⊕ Fin 1) → β := k ∘ j₂
      have keepLower : Preserves Γ₁ join Δ := keepsComp Γ₁ Γ₂ Δ j₂ k baseKeeps keep
      have keepParams : Preserves Γ (join ∘ j₁) Δ :=
        keepsComp Γ Γ₁ Δ j₁ join (freshKeeps Γ lower) keepLower
      have relocated := renameInto hBelow join Δ keepLower
      change Nonempty (Derivation B Δ ((below (lift (foldMotive theta)) n).relabel join)) at relocated
      rw [belowRename] at relocated
      obtain ⟨hb⟩ := relocated
      have atTail := Derivation.universalElimination (emb t) hb
      rw [belowElimSyntax,relocatedFoldMotiveAt] at atTail
      have bound : Nonempty (Derivation B Δ (ltF t (n.relabel join))) := by
        simpa only [n₂,join,j₂,Term.relabel_relabel] using strict
      obtain ⟨bound⟩ := bound
      have tailFormula := eliminateParsedMotive theta (fun i => .var ((join ∘ j₁) i))
        t st Δ ⟨Derivation.implicationElimination atTail bound⟩ tail
      have made := cases.consCase β (join ∘ j₁) Δ (n₂.relabel k) (s.relabel k) h t st
        keepParams cell shape eqRaw strict tail scratch tailFormula
      simpa only [pairAtRename,r,join,j₁,j₂,Function.comp_apply,Term.relabel] using made
  obtain ⟨progress⟩ := progress
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction progress)⟩

/-- Specialization retains the actual positive parse of the original raw
term in the same source calculus. There is no host list argument. -/
theorem exact_OriginalSparseParsedFold (theta : Formula (α ⊕ Fin 2))
    (cases : ParsedFoldCases B Γ theta) (n s : OTerm α)
    (seen : Report (B := B) (Γ := Γ) parser (suc s) ![n]) :
    Nonempty (Derivation B Γ (pairAt theta Term.var n s)) := by
  obtain ⟨all⟩ := exact_OriginalSparseParsedFoldAll theta cases
  have atRaw := Derivation.universalElimination (emb n) all
  rw [foldMotiveAt] at atRaw
  exact eliminateParsedMotive theta Term.var n s Γ ⟨atRaw⟩ seen

#print axioms exact_OriginalSparseParsedFoldAll
#print axioms exact_OriginalSparseParsedFold

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseParsedFoldProof
