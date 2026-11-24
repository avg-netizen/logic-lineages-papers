module

public import LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawRepackProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseParsedFoldProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawRepackInverseProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (programSubst)
open ID1Completion.InternalControlGraphSupportProof (zeroValue outputTransport headTransport valueUnique)
open ID1Completion.InternalRawListRecursionProof (nilValue consValue)
open NumberedWindowInternalSparsePathEnvelopeTargets (z rawCons)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparseParsedFoldSyntaxProof (pairAt positiveGraph)
open NumberedWindowInternalSparseParsedFoldProof (ParsedFoldCases exact_OriginalSparseParsedFold)
open NumberedWindowInternalFunctionalRawRepack (repack)
open NumberedWindowInternalFunctionalRawRepackProof (repackGraph exact_FunctionalRawRepackParser)

attribute [local irreducible] programGraph

private def motive {α : Type} : Formula (α ⊕ Fin 2) :=
  repackGraph (.var (.inr 0)) (.var (.inr 1))

private theorem motiveAt {α β : Type} (r : α → OTerm β) (raw scratch : OTerm β) :
    pairAt motive r raw scratch = repackGraph raw scratch := by
  unfold pairAt motive repackGraph
  rw [programSubst]
  congr 1
  funext i
  exact Fin.cases rfl (fun k => Fin.elim0 k) i

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Reverse the exact contract of fixed repack on every successful original
raw parser report. Conditions are arithmetic derivations on symbolic raw
and scratch terms, not semantic numeric witnesses. -/
theorem exact_FunctionalRawRepackOfParser (raw scratch : OTerm α)
    (held : Nonempty (Derivation B Γ (positiveGraph raw scratch))) :
    Nonempty (Derivation B Γ (repackGraph raw scratch)) := by
  have cases : ParsedFoldCases B Γ motive := by
    constructor
    · intro β j Δ n s keep raw0 scratch0
      rw [motiveAt]
      have same : Nonempty (Derivation B Δ (repackGraph z z)) :=
        nilValue (body := B) (Gamma := Δ) .zero fieldCons z Fin.elim0 (zeroValue Fin.elim0)
      obtain ⟨e₁⟩ := raw0
      obtain ⟨e₂⟩ := scratch0
      have prepare := headTransport repack z z s Fin.elim0 ⟨symm e₂⟩ same
      exact outputTransport repack z n (Fin.cons s Fin.elim0) ⟨symm e₁⟩ prepare
    · intro β j Δ n s head tail st keep _ _ canonical _ _ scratchStep inner
      rw [motiveAt] at inner ⊢
      have field := NumberedWindowInternalSparsePairGraphProof.consGraph
        (body := B) (Γ := Δ) head tail
      obtain ⟨e⟩ := canonical
      have actual := outputTransport fieldCons (rawCons head tail) n ![head,tail] ⟨symm e⟩ field
      exact consValue .zero fieldCons s head st tail n Fin.elim0 scratchStep inner actual
  have claimed := exact_OriginalSparseParsedFold motive cases raw scratch held
  rw [motiveAt] at claimed
  exact claimed

theorem exact_FunctionalRawRepackEquivalent (raw scratch : OTerm α) :
    Nonempty (Derivation B Γ (positiveGraph raw scratch)) ↔
      Nonempty (Derivation B Γ (repackGraph raw scratch)) :=
  ⟨exact_FunctionalRawRepackOfParser raw scratch,exact_FunctionalRawRepackParser raw scratch⟩

/-- The literal positive parser has only one raw input for a held
scratch tape, proved using actual parser and repacker functionality. -/
theorem exact_PositiveRawParserInjective (raw other scratch : OTerm α)
    (a : Nonempty (Derivation B Γ (positiveGraph raw scratch)))
    (b : Nonempty (Derivation B Γ (positiveGraph other scratch))) :
    Nonempty (Derivation B Γ (eqn raw other)) :=
  valueUnique repack raw other (Fin.cons scratch Fin.elim0)
    (exact_FunctionalRawRepackOfParser raw scratch a) (exact_FunctionalRawRepackOfParser other scratch b)

#print axioms exact_FunctionalRawRepackOfParser
#print axioms exact_FunctionalRawRepackEquivalent
#print axioms exact_PositiveRawParserInjective
end LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawRepackInverseProof
