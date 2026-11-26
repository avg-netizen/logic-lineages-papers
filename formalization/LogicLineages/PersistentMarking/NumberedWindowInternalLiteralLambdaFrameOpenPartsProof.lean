module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaFrameProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionGuardFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaFrameOpenPartsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBodyRename rawConsRename moveReports Reports)
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw frameSlot sameSlot)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralFunctionGuardFieldsProof (nodeAtCases moveBit equalityAt)
open NumberedWindowInternalLiteralBetaLeafProof (rawLambdaShape)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralLambdaFrameProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem rawLambdaRename {β : Type} (d a : OTerm α) (j : α → β) :
    (rawLambdaTerm d a).relabel j = rawLambdaTerm (d.relabel j) (a.relabel j) := by
  simp only [rawLambdaTerm,rawConsRename,numeralRename,packedBodyRename,List.map_cons,List.map_nil]

theorem lambdaWitnessRename {β : Type} (w : OTerm α) (j : α → β) :
    (lambdaWitnessTerm w).relabel j = lambdaWitnessTerm (w.relabel j) := by
  simp only [lambdaWitnessTerm,rawConsRename,numeralRename,packedBodyRename,List.map_cons,List.map_nil]

structure LambdaParts (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (q w r d a child e b : OTerm α) : Prop where
  source : D B Γ (eqn q (rawLambdaTerm d a))
  witness : D B Γ (eqn w (lambdaWitnessTerm child))
  target : D B Γ (eqn r (rawLambdaTerm e b))
  binder : D B Γ (eqn d e)
  sourceSlot : D B Γ (programGraph (frameSlot 1 0) a ![q,w,r])
  childSlot : D B Γ (programGraph (frameSlot 0 1) child ![q,w,r])
  targetSlot : D B Γ (programGraph (frameSlot 1 2) b ![q,w,r])

private theorem oneField {T : Type} (vs : List T) (size : vs.length = 1) : ∃ a, vs = [a] := by
  rcases vs with _ | ⟨a,_ | ⟨b,bs⟩⟩ <;> simp at size
  exact ⟨a,rfl⟩

private theorem twoFields {T : Type} (vs : List T) (size : vs.length = 2) : ∃ a b, vs = [a,b] := by
  rcases vs with _ | ⟨a,_ | ⟨b,_ | ⟨c,cs⟩⟩⟩ <;> simp at size
  exact ⟨a,b,rfl⟩

/-- Recover a real binder scope, both original lambda bodies and the
exact tag-one child certificate, on the same original raw tape. -/
theorem exact_OpenLambdaFrameParts (q w r : OTerm α) (goal : Formula α)
    (checked : D B Γ (bit lambdaWitnessTest ![q,w,r]))
    (held : D B Γ (bit lambdaFrameGuard ![q,w,r]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (d a child e b : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      LambdaParts B Δ (q.relabel j) (w.relabel j) (r.relabel j) d a child e b →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  let xs : Fin 3 → OTerm α := ![q,w,r]
  obtain ⟨pair⟩ := conjunctionRecover _ _ xs held
  obtain ⟨rest⟩ := conjunctionRecover _ _ xs ⟨Derivation.conjunctionRight pair⟩
  have lShape : D B Γ (bit (onRaw rawLambdaShape 0) xs) := ⟨Derivation.conjunctionLeft pair⟩
  have rShape : D B Γ (bit (onRaw rawLambdaShape 2) xs) := ⟨Derivation.conjunctionLeft rest⟩
  have same : D B Γ (bit (sameSlot 0) xs) := ⟨Derivation.conjunctionRight rest⟩
  apply nodeAtCases 1 1 1 ![q,w,r] goal checked
  intro β j Δ ws keep₁ n₁ wit iw
  obtain ⟨child,rfl⟩ := oneField ws n₁
  let q₁ := q.relabel j
  let w₁ := w.relabel j
  let r₁ := r.relabel j
  have leftShape := moveBit _ q w r j Δ keep₁ lShape
  have rightShape := moveBit _ q w r j Δ keep₁ rShape
  have eq₁ := moveBit _ q w r j Δ keep₁ same
  apply nodeAtCases 2 2 0 ![q₁,w₁,r₁] (goal.relabel j) leftShape
  intro γ k Θ ls keep₂ n₂ sl il
  obtain ⟨dom,a,rfl⟩ := twoFields ls n₂
  let q₂ := q₁.relabel k
  let w₂ := w₁.relabel k
  let r₂ := r₁.relabel k
  have rightShape₂ := moveBit _ q₁ w₁ r₁ k Θ keep₂ rightShape
  have eq₂ := moveBit _ q₁ w₁ r₁ k Θ keep₂ eq₁
  apply nodeAtCases 2 2 2 ![q₂,w₂,r₂] ((goal.relabel j).relabel k) rightShape₂
  intro δ l Ω rs keep₃ n₃ sr ir
  obtain ⟨dom',b,rfl⟩ := twoFields rs n₃
  let q₃ := q₂.relabel l
  let w₃ := w₂.relabel l
  let r₃ := r₂.relabel l
  let tape : Fin 3 → OTerm δ := ![q₃,w₃,r₃]
  let d := dom.relabel l
  let before := a.relabel l
  let inner := (child.relabel k).relabel l
  have eq₃ := moveBit _ q₂ w₂ r₂ l Ω keep₃ eq₂
  have L := moveReports l Ω keep₃ q₂ _ [dom,a] il
  have W := moveReports (l ∘ k) Ω (fun f hf => by
    simpa only [formulaRelabelComposition] using keep₃ _ (keep₂ f hf)) w₁ _ [child] iw
  have word : Reports B Ω w₃ cellTail [inner] := by
    simpa only [List.map_cons,List.map_nil,← Term.relabel_relabel] using W
  have left : D B Ω (eqn q₃ (rawLambdaTerm d before)) := by
    change D B Θ (eqn q₂ (rawLambdaTerm dom a)) at sl
    have t := renameInto sl l Ω keep₃
    simpa only [eqnRelabel,rawLambdaRename] using t
  have middle : D B Ω (eqn w₃ (lambdaWitnessTerm inner)) := by
    change D B Δ (eqn w₁ (lambdaWitnessTerm child)) at wit
    have t := renameInto wit k Θ keep₂
    rw [eqnRelabel,lambdaWitnessRename] at t
    have rt := renameInto t l Ω keep₃
    simpa only [eqnRelabel,lambdaWitnessRename] using rt
  have right : D B Ω (eqn r₃ (rawLambdaTerm dom' b)) := sr
  have domEq := equalityAt tape 0 d dom' (onTape (field 0) 0 d tape L.1)
    (onTape (field 0) 2 dom' tape ir.1) eq₃
  let composed := l ∘ k ∘ j
  have keep (f : Formula α) (hf : f ∈ Γ) : f.relabel composed ∈ Ω := by
    simpa only [composed,formulaRelabelComposition,Function.comp_assoc] using keep₃ _ (keep₂ _ (keep₁ f hf))
  have row : LambdaParts B Ω q₃ w₃ r₃ d before inner dom' b :=
    ⟨left,middle,right,domEq,onTape (field 1) 0 before tape L.2.1,
      onTape (field 0) 1 inner tape word.1,onTape (field 1) 2 b tape ir.2.1⟩
  have row' : LambdaParts B Ω (q.relabel composed) (w.relabel composed) (r.relabel composed) d before inner dom' b := by
    simpa only [q₃,w₃,r₃,q₂,w₂,r₂,q₁,w₁,r₁,composed,Term.relabel_relabel,Function.comp_assoc] using row
  have done := use δ composed Ω d before inner dom' b keep row'
  simpa only [composed,formulaRelabelComposition,Function.comp_assoc] using done

#print axioms rawLambdaRename
#print axioms lambdaWitnessRename
#print axioms exact_OpenLambdaFrameParts
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaFrameOpenPartsProof
