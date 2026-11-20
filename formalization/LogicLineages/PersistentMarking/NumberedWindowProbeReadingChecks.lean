module
public import LogicLineages.PersistentMarking.NumberedWindowProbeReadingTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticProgramProof
import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperatorsSupportProof
public section
namespace LogicLineages.PersistentMarking.NumberedWindowProbeReadingChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalControlGraph ID1Completion.InternalCalculus
open PositiveArithmeticOperators PositiveArithmeticOperatorsSupportProof SourceComputabilityFormulaSupportProof
open NumberedWindowInternalProbeTargets NumberedWindowProbeReadingTargets
open NumberedWindowComputabilityFormulaTargets (accepts)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

theorem exact_ProbeTypeCoding : ExactProbeTypeCoding := by
  intro τ
  induction τ with
  | ground => rfl
  | arrow σ τ ihσ ihτ => simp [typeCode,NumberedWindowProbeCode.code,ihσ,ihτ]

private theorem existentialNat {α : Type} (phi : Formula (α ⊕ Fin 1)) (P : Nat → Prop) (env : α → Nat) :
    realize P (existsOne phi) env ↔ ∃ x : Nat, realize P phi (Sum.elim env fun _ => x) := by
  rw [existsOneTruth]
  constructor
  · rintro ⟨xs,h⟩
    refine ⟨xs 0,?_⟩
    have e : xs = fun _ => xs 0 := funext (fun i => congrArg xs (Subsingleton.elim i 0))
    rwa [← e]
  · rintro ⟨x,h⟩
    exact ⟨fun _ => x,h⟩

private theorem typedTruth {α : Type} (h : Program 2) (τ : LogicLineages.OrdinalComparison.Source.Ty)
    (q : OTerm α) (P : Nat → Prop) (env : α → Nat) :
    realize P (typedAt h τ q) env ↔ evaluate h (NumberedWindowProbeCode.code τ ::ᵥ q.realize env ::ᵥ nil) = 1 := by
  rw [typedAt,programGraph,ID1Completion.InternalGraphComposition.graph,embeddingTruth,
    OrdinaryArithmeticProgramProof.appliedProgramGraphTruth,exact_ProbeTypeCoding]
  change evaluate h ((numeral (NumberedWindowProbeCode.code τ)).realize env ::ᵥ q.realize env ::ᵥ nil) =
    (numeral 1).realize env ↔ _
  rw [numeralTruth,numeralTruth]

private theorem freshTruth {α : Type} (a : Program 1) (q u : OTerm α) (P : Nat → Prop) (env : α → Nat) :
    realize P (freshAt a q u) env ↔ evaluate a (q.realize env ::ᵥ nil) = (u.realize env).succ := by
  rw [freshAt,programGraph,ID1Completion.InternalGraphComposition.graph,embeddingTruth,
    OrdinaryArithmeticProgramProof.appliedProgramGraphTruth]
  rfl

private theorem appTruth {α : Type} (p : Program 3) (q u v : OTerm α) (P : Nat → Prop) (env : α → Nat) :
    realize P (accepts p q u v) env ↔ evaluate p (q.realize env ::ᵥ u.realize env ::ᵥ v.realize env ::ᵥ nil) = 1 := by
  rw [accepts,embeddingTruth,OrdinaryArithmeticProgramProof.appliedProgramGraphTruth]
  rfl

private theorem optionOutput (n : Option Nat) (u : Nat) :
    Encodable.encode n = u.succ ↔ n = some u := by
  cases n <;> simp

private theorem boolOutput (b : Bool) : b.toNat = 1 ↔ b = true := by cases b <;> decide

theorem exact_ProbeReading : ExactProbeReading := by
  intro ty pick app h a p ht ha hp τ α q P env
  constructor
  · rw [typedTruth,ht,boolOutput]
  · simp only [witnesses,existentialNat,generalConjTruth,typedTruth,freshTruth,appTruth,
      FirstOrder.Language.Term.realize_relabel,FirstOrder.Language.Term.realize,Sum.elim_inl,Sum.elim_inr,
      Function.comp_def,ht,ha,hp,boolOutput,optionOutput]

#print axioms exact_ProbeTypeCoding
#print axioms exact_ProbeReading
end LogicLineages.PersistentMarking.NumberedWindowProbeReadingChecks
