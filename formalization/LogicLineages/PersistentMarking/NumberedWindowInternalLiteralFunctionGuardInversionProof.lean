module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionGuardFieldsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenGuardProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionGuardInversionProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel zRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (moveReports rawConsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalSparseRawFunctionFrame
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalSparseRawFunctionFrameOpenGuardProof (Ready)
open NumberedWindowInternalLiteralFunctionGuardFieldsProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Literal tags and ordered raw fields are retained at the two
endpoints and original witness. The equalities compare the two actual
annotations and the two actual raw argument fields, not class addresses.
The three actual frame emitters select the already-bound components. -/
structure Parts (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (q w r dom cod fn arg child dom' cod' dest arg' : OTerm α) : Prop where
  source : D B Γ (eqn q (auxiliaryTerm dom cod fn arg))
  witness : D B Γ (eqn w (functionWitnessTerm child))
  target : D B Γ (eqn r (auxiliaryTerm dom' cod' dest arg'))
  domEq : D B Γ (eqn dom dom')
  codEq : D B Γ (eqn cod cod')
  argEq : D B Γ (eqn arg arg')
  ready : Ready B Γ ![q,w,r] fn child dest

private theorem witnessRename {β : Type} (w : OTerm α) (j : α → β) :
    (functionWitnessTerm w).relabel j = functionWitnessTerm (w.relabel j) := by
  simp only [functionWitnessTerm,rawConsRename,numeralRename,zRelabel]

private theorem oneField {T : Type} (vs : List T) (size : vs.length = 1) :
    ∃ a, vs = [a] := by
  rcases vs with _ | ⟨a,_ | ⟨b,bs⟩⟩
  · simp at size
  · exact ⟨a,rfl⟩
  · simp at size

private theorem fourFields {T : Type} (vs : List T) (size : vs.length = 4) :
    ∃ a b c d, vs = [a,b,c,d] := by
  rcases vs with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,_ | ⟨e,es⟩⟩⟩⟩⟩ <;> simp at size
  exact ⟨a,b,c,d,rfl⟩

/-- Open elimination of a successful actual function-context guard.
Both arbitrary positive annotations, the terms, and the raw witness
are separated by the original graph, in the original argument order. -/
theorem exact_OpenFunctionGuardParts (q w r : OTerm α) (goal : Formula α)
    (held : D B Γ (bit frameGood ![q,w,r]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (dom cod fn arg child dom' cod' dest arg' : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Parts B Δ (q.relabel j) (w.relabel j) (r.relabel j)
        dom cod fn arg child dom' cod' dest arg' →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  have tests := guardChecks ![q,w,r] held
  apply nodeAtCases 5 1 1 ![q,w,r] goal tests.witness
  intro β j Δ ws keep₁ n₁ wit iw
  obtain ⟨child,rfl⟩ := oneField ws n₁
  let q₁ := q.relabel j
  let w₁ := w.relabel j
  let r₁ := r.relabel j
  have t₁ := moveChecks q w r j Δ keep₁ tests
  apply nodeAtCases 6 4 0 ![q₁,w₁,r₁] (goal.relabel j) t₁.source
  intro γ k Θ ls keep₂ n₂ sl il
  obtain ⟨dom,cod,fn,arg,rfl⟩ := fourFields ls n₂
  let q₂ := q₁.relabel k
  let w₂ := w₁.relabel k
  let r₂ := r₁.relabel k
  have t₂ := moveChecks q₁ w₁ r₁ k Θ keep₂ t₁
  apply nodeAtCases 6 4 2 ![q₂,w₂,r₂] ((goal.relabel j).relabel k) t₂.target
  intro δ l Ω rs keep₃ n₃ sr ir
  obtain ⟨dom',cod',dest,arg',rfl⟩ := fourFields rs n₃
  let q₃ := q₂.relabel l
  let w₃ := w₂.relabel l
  let r₃ := r₂.relabel l
  let xs : Fin 3 → OTerm δ := ![q₃,w₃,r₃]
  let dd := dom.relabel l
  let cc := cod.relabel l
  let ff := fn.relabel l
  let aa := arg.relabel l
  let ww := (child.relabel k).relabel l
  have t₃ := moveChecks q₂ w₂ r₂ l Ω keep₃ t₂
  have L := moveReports l Ω keep₃ q₂ _ [dom,cod,fn,arg] il
  have W := moveReports (l ∘ k) Ω (fun f hf => by
    simpa only [formulaRelabelComposition] using keep₃ _ (keep₂ f hf)) w₁ _ [child] iw
  have wReport : NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof.Reports
      B Ω w₃ NumberedWindowInternalSparseFieldCell.cellTail [ww] := by
    simpa only [List.map_cons,List.map_nil,← Term.relabel_relabel] using W
  have left : D B Ω (eqn q₃ (auxiliaryTerm dd cc ff aa)) := by
    change D B Θ (eqn q₂ (auxiliaryTerm dom cod fn arg)) at sl
    have m' := renameInto sl l Ω keep₃
    simpa only [eqnRelabel,auxiliaryRename] using m'
  have mid : D B Ω (eqn w₃ (functionWitnessTerm ww)) := by
    change D B Δ (eqn w₁ (functionWitnessTerm child)) at wit
    have wa := renameInto wit k Θ keep₂
    rw [eqnRelabel,witnessRename] at wa
    have wb := renameInto wa l Ω keep₃
    simpa only [eqnRelabel,witnessRename] using wb
  have right : D B Ω (eqn r₃ (auxiliaryTerm dom' cod' dest arg')) := sr
  have ed := equalityAt xs 0 dd dom' (onTape (field 0) 0 dd xs L.1)
    (onTape (field 0) 2 dom' xs ir.1) t₃.dom
  have ec := equalityAt xs 1 cc cod' (onTape (field 1) 0 cc xs L.2.1)
    (onTape (field 1) 2 cod' xs ir.2.1) t₃.cod
  have ea := equalityAt xs 3 aa arg' (onTape (field 3) 0 aa xs L.2.2.2.1)
    (onTape (field 3) 2 arg' xs ir.2.2.2.1) t₃.arg
  have ready : Ready B Ω xs ff ww dest :=
    ⟨moveBit _ q₂ w₂ r₂ l Ω keep₃ (moveBit _ q₁ w₁ r₁ k Θ keep₂ (moveBit _ q w r j Δ keep₁ held)),
      onTape (field 2) 0 ff xs L.2.2.1,onTape (field 0) 1 ww xs wReport.1,
      onTape (field 2) 2 dest xs ir.2.2.1⟩
  let comp := l ∘ k ∘ j
  have keep (f : Formula α) (hf : f ∈ Γ) : f.relabel comp ∈ Ω := by
    simpa only [comp,formulaRelabelComposition,Function.comp_assoc] using keep₃ _ (keep₂ _ (keep₁ f hf))
  have parts : Parts B Ω q₃ w₃ r₃ dd cc ff aa ww dom' cod' dest arg' :=
    ⟨left,mid,right,ed,ec,ea,ready⟩
  have parts' : Parts B Ω (q.relabel comp) (w.relabel comp) (r.relabel comp)
      dd cc ff aa ww dom' cod' dest arg' := by
    simpa only [q₃,w₃,r₃,q₂,w₂,r₂,q₁,w₁,r₁,comp,Term.relabel_relabel,Function.comp_assoc] using parts
  have result := use δ comp Ω dd cc ff aa ww dom' cod' dest arg' keep parts'
  simpa only [comp,formulaRelabelComposition,Function.comp_assoc] using result

#print axioms exact_OpenFunctionGuardParts
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionGuardInversionProof
