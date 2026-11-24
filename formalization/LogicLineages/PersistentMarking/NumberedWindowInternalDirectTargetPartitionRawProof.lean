module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetPartitionRawTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetPartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionAppendProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsMapCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetPartitionRawProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalDirectSourcePartitionRawTargets
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (chosenParserCases keepThrough renameUnit renameParser)
open NumberedWindowInternalDirectSourcePartitionAppendProof (exact_OpenSourcePartitionAppend)
open NumberedWindowInternalDirectInsertedTargetsMapCases (exactOpenRawMapCases)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (insertedTargets scratchTargets)
open NumberedWindowInternalDirectTargetPartitionRawTargets
open NumberedWindowInternalDirectTargetPartitionRawGraphProof (mappedCases recoverObserver)

attribute [local irreducible] programGraph

private theorem renameUnary {B : Positive (Fin 1)} {α β : Type}
    {Γ : List (Formula α)} {Δ : List (Formula β)} (p : Program 1) (raw out : OTerm α)
    (h : Nonempty (Derivation B Γ (unary p (suc out) raw)))
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    Nonempty (Derivation B Δ (unary p (suc (out.relabel j)) (raw.relabel j))) := by
  simpa only [unaryRename,sucRelabel] using renameInto h j Δ keep

private theorem finish (test : Program 2) (B : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (t k a dt dk projected : OTerm α) (goal : Formula α)
    (pt : Nonempty (Derivation B Γ (unary NumberedWindowInternalSparseFieldParser.parser (suc dt) t)))
    (pk : Nonempty (Derivation B Γ (unary NumberedWindowInternalSparseFieldParser.parser (suc dk) k)))
    (pa : Nonempty (Derivation B Γ (unary insertedTargets (suc projected) a)))
    (run : Nonempty (Derivation B Γ (programGraph (observePartition test) (suc z)
      (sourceTape dt dk projected))))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (dT dK dI p joined : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Reports test B Δ (t.relabel j) (k.relabel j) (a.relabel j) dT dK dI p joined →
      Nonempty (Derivation B Δ (goal.relabel j))) : Nonempty (Derivation B Γ goal) := by
  apply exact_OpenSourcePartitionAppend test dt dk projected goal run
  intro β j Δ joined keep appended seen
  let A := a.relabel j
  let P := projected.relabel j
  have raw := renameUnary insertedTargets a projected pa j keep
  apply exactOpenRawMapCases B β Δ A P (goal.relabel j) raw
  intro γ l Ω di retain parsed scratch
  let ρ := l ∘ j
  have t' := renameParser t dt pt ρ Ω (keepThrough j l keep retain)
  have k' := renameParser k dk pk ρ Ω (keepThrough j l keep retain)
  have a' := renameUnary insertedTargets a projected pa ρ (keepThrough j l keep retain)
  have ap := renameInto appended l Ω retain
  have obs := renameInto seen l Ω retain
  rw [formulaRelabelComposition]
  apply next γ ρ Ω (dt.relabel ρ) (dk.relabel ρ) di (projected.relabel ρ) (joined.relabel l)
    (keepThrough j l keep retain)
  refine ⟨t',k',?_,a',?_,?_,?_⟩
  · simpa only [A,ρ,Term.relabel_relabel] using parsed
  · simpa only [P,ρ,Term.relabel_relabel] using scratch
  · simpa only [ID1Completion.InternalControlGraphSupportProof.programRename,
      NumberedWindowInternalSparseFieldParserOpenSyntaxProof.binaryInputsRename,
      ρ,Term.relabel_relabel] using ap
  · simpa only [ID1Completion.InternalControlGraphSupportProof.programRename,
      NumberedWindowInternalSparseFieldParserOpenSyntaxProof.binaryInputsRename,
      ID1Completion.InternalTagArithmeticSyntaxProof.zRelabel,sucRelabel,ρ,Term.relabel_relabel] using obs

theorem exactOpenRawTargetCheck : ExactOpenRawTargetCheck := by
  intro test B α Γ t k a goal held next
  let xs := sourceTape t k a
  obtain ⟨both⟩ := conjunctionRecover allReady (decodeCall test) xs held
  obtain ⟨ready⟩ := conjunctionRecover (parsedAt 0) (conjunction (parsedAt 1) mapReady) xs
    ⟨Derivation.conjunctionLeft both⟩
  obtain ⟨rest⟩ := conjunctionRecover (parsedAt 1) mapReady xs ⟨Derivation.conjunctionRight ready⟩
  have call := Derivation.conjunctionRight both
  apply chosenParserCases 0 t k a goal ⟨Derivation.conjunctionLeft ready⟩
  intro β j Δ dt hj pt
  let t₁ := t.relabel j
  let k₁ := k.relabel j
  let a₁ := a.relabel j
  have pk₁ := renameUnit (parsedAt 1) t k a ⟨Derivation.conjunctionLeft rest⟩ j Δ hj
  have pr₁ := renameUnit mapReady t k a ⟨Derivation.conjunctionRight rest⟩ j Δ hj
  have call₁ := renameUnit (decodeCall test) t k a ⟨call⟩ j Δ hj
  apply chosenParserCases 1 t₁ k₁ a₁ (goal.relabel j) pk₁
  intro γ l Θ dk hl pk
  let t₂ := t₁.relabel l
  let k₂ := k₁.relabel l
  let a₂ := a₁.relabel l
  have pt₂ := renameParser t₁ dt pt l Θ hl
  have pr₂ := renameUnit mapReady t₁ k₁ a₁ pr₁ l Θ hl
  have call₂ := renameUnit (decodeCall test) t₁ k₁ a₁ call₁ l Θ hl
  apply mappedCases t₂ k₂ a₂ ((goal.relabel j).relabel l) pr₂
  intro δ m Ω projected hm pa
  let t₃ := t₂.relabel m
  let k₃ := k₂.relabel m
  let a₃ := a₂.relabel m
  let dt₃ := (dt.relabel l).relabel m
  let dk₃ := dk.relabel m
  have pt₃ := renameParser t₂ (dt.relabel l) pt₂ m Ω hm
  have pk₃ := renameParser k₂ dk pk m Ω hm
  have ran := recoverObserver test t₃ k₃ a₃ dt₃ dk₃ projected pt₃ pk₃ pa
    (renameUnit (decodeCall test) t₂ k₂ a₂ call₂ m Ω hm)
  let ρ := m ∘ (l ∘ j)
  have keepρ := keepThrough (l ∘ j) m (keepThrough j l hj hl) hm
  rw [formulaRelabelComposition j l goal,formulaRelabelComposition (l ∘ j) m goal]
  apply finish test B δ Ω t₃ k₃ a₃ dt₃ dk₃ projected (goal.relabel ρ) pt₃ pk₃ pa ran
  intro ε n Λ dT dK dI pr joined retain reports
  rw [formulaRelabelComposition]
  apply next ε (n ∘ ρ) Λ dT dK dI pr joined (keepThrough ρ n keepρ retain)
  have assocl : ((m ∘ l) ∘ j) = ρ := rfl
  have assocn : ((n ∘ m) ∘ l) ∘ j = n ∘ ρ := rfl
  simpa only [t₃,k₃,a₃,t₂,k₂,a₂,t₁,k₁,a₁,Term.relabel_relabel,assocl,assocn] using reports

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetPartitionRawProof
