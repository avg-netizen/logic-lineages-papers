module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksBindingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalFiniteBlocks
open SourceComputabilityFormulaSupportProof InternalBinderTransportSyntaxProof InternalBinderTransportProof
open InternalPositiveUnfoldingSupportProof InternalTermSubstitutionSyntaxProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksBindingProof

theorem existsSubst {α β : Type} (phi : Formula (α ⊕ Fin 1)) (ts : α → Term β) :
    (existsOne phi).subst ts = existsOne (phi.subst
      (Sum.elim (fun a => (ts a).relabel Sum.inl) (fun i => .var (.inr i)))) := by
  change ((allOne phi.not).subst ts).not = _
  rw [actualUniversalSubstitution]
  rfl

def witnessesBeforeLast {α : Type} {k : Nat} (ts : Fin (k+1) → Term α) : α ⊕ Fin k → Term α :=
  Sum.elim Term.var (fun i => ts i.castSucc)

theorem witnessLast {α : Type} (k : Nat) (phi : Formula (α ⊕ Fin (k+1))) (ts : Fin (k+1) → Term α) :
    instantiate ((phi.relabel (splitLast k)).subst
      (Sum.elim (fun a => (witnessesBeforeLast ts a).relabel Sum.inl) (fun i : Fin 1 => .var (.inr i))))
      (ts (Fin.last k)) = phi.subst (Sum.elim Term.var ts) := by
  rw [instantiate,formulaSubstComposition,actualRelabelSubstitution]
  congr 1
  funext a
  cases a with
  | inl a => rfl
  | inr i =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Function.comp_apply,splitLast,Sum.elim_inr,Fin.lastCases_last,Term.subst]
    · simp only [Function.comp_apply,splitLast,Sum.elim_inr,Fin.lastCases_castSucc,Sum.elim_inl]
      rw [termRelabelSubst]
      exact termSubstVar _

theorem zeroWitness {α : Type} (phi : Formula (α ⊕ Fin 0)) (ts : Fin 0 → Term α) :
    phi.subst (Sum.elim Term.var ts) = phi.relabel eraseZero := by
  rw [formulaRelabelAsSubst]
  congr 1
  funext a
  cases a with
  | inl a => rfl
  | inr i => exact Fin.elim0 i

theorem renameIdentity {α : Type} (phi : Formula α) : phi.relabel id = phi := by
  rw [formulaRelabelAsSubst]
  change phi.subst Term.var = phi
  exact formulaSubstVar phi

theorem parametersZero {α : Type} (phi : Formula α) :
    (phi.relabel (Sum.inl : α → α ⊕ Fin 0)).relabel eraseZero = phi := by
  rw [formulaRelabelComposition]
  exact renameIdentity phi

theorem parametersLast {α : Type} (k : Nat) (phi : Formula α) :
    (phi.relabel (Sum.inl : α → α ⊕ Fin (k+1))).relabel (splitLast k) =
      weaken (phi.relabel (Sum.inl : α → α ⊕ Fin k)) := by
  rw [formulaRelabelComposition,weaken,formulaRelabelComposition]
  rfl

theorem contextZero {α : Type} (Gamma : List (Formula α)) :
    (Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 0))).map (fun p => p.relabel eraseZero) = Gamma := by
  simp only [List.map_map]
  have h : ((fun p : Formula (α ⊕ Fin 0) => p.relabel eraseZero) ∘
      (fun p : Formula α => p.relabel (Sum.inl : α → α ⊕ Fin 0))) = id := by
    funext p
    exact parametersZero p
  rw [h,List.map_id]

theorem contextLast {α : Type} (k : Nat) (Gamma : List (Formula α)) :
    (Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin (k+1)))).map (fun p => p.relabel (splitLast k)) =
      (Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin k))).map weaken := by
  simp only [List.map_map]
  congr 1
  funext p
  exact parametersLast k p

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof
