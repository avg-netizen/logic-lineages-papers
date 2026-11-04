module
public import LogicLineages.OrdinalComparison.SourcePlanPrefixCodeTargets
public import LogicLineages.OrdinalComparison.ContextInsertionCodeSemanticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePlanPrefixCode.Proof
open SyntaxCode

theorem erase_rename_indices {Γ Δ Λ τ} (t : OriginalTerm Γ τ) (r : Renaming Γ Δ) (s : Renaming Γ Λ)
    (h : ∀ (σ : Ty) (x : Variable Γ σ),SourceTypedPorts.variableIndex (r x)=SourceTypedPorts.variableIndex (s x)) :
    erase (t.rename r)=erase (t.rename s) := by
  induction t generalizing Δ Λ with
  | var x => exact congrArg Raw.var (h _ x)
  | app f a ihf iha => exact congrArg₂ Raw.app (ihf r s h) (iha r s h)
  | @lam Γ σ τ t ih =>
    apply congrArg (Raw.lam (typeCode σ))
    apply ih (Renaming.lift r) (Renaming.lift s)
    intro υ x
    cases x with
    | here => rfl
    | there x => exact congrArg (fun i => i+1) (h _ x)
  | zeroC => rfl
  | succC => rfl
  | caseC τ => rfl
  | recC τ => rfl
  | ranked tag args ih => cases tag

theorem prefix_correct {Γ Δ} (k : Nat) (r : Renaming Γ Δ)
    (h : ∀ (τ : Ty) (x : Variable Γ τ),SourceTypedPorts.variableIndex (r x)=SourceTypedPorts.variableIndex x+k)
    {τ} (t : OriginalTerm Γ τ) :
    ContextInsertionCode.sourceCode 0 k (encodeTerm t)=encodeTerm (t.rename r) := by
  have hh := ContextInsertionCode.Proof.exactSourceInsertion [] (List.replicate k Ty.ground) Γ τ t
  simp only [List.length_nil,List.length_replicate] at hh
  apply Eq.trans hh
  apply congrArg code
  apply erase_rename_indices
  intro σ x
  have hi := ContextInsertionCode.Proof.insertion_index [] (List.replicate k Ty.ground) Γ x
  have hr := h σ x
  simp only [List.length_nil,List.length_replicate,ContextInsertionCode.indexCode,Nat.not_lt_zero,ite_false] at hi
  exact hi.trans hr.symm

theorem exactPrefixCalibration : Targets.ExactPrefixCalibration := by
  intro Γ Δ k r h
  refine ⟨fun τ t => prefix_correct k r h t,?_⟩
  intro es
  simp only [shiftPairs,List.map_map]
  apply List.map_congr_left
  intro p hp
  change (ContextInsertionCode.sourceCode 0 k (encodeTerm p.1),ContextInsertionCode.sourceCode 0 k (encodeTerm p.2)) =
    (encodeTerm (p.1.rename r),encodeTerm (p.2.rename r))
  rw [prefix_correct k r h,prefix_correct k r h]
end LogicLineages.OrdinalComparison.Source.SourcePlanPrefixCode.Proof
