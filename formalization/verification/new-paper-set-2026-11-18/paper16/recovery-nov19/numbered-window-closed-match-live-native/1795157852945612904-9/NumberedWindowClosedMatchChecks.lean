module
public import LogicLineages.PersistentMarking.NumberedWindowClosedMatchTargets
import LogicLineages.PersistentMarking.NumberedWindowNumeralGraphChecks
import LogicLineages.PersistentMarking.NumberedWindowTypeFormulaSubstitutionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
public section
namespace LogicLineages.PersistentMarking.NumberedWindowClosedMatchChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalTagArithmeticSyntaxProof (emb suc z bindEmbedding liftBind varBind)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (existsEmbeddedSubst liftTermSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowTypeFormulaSubstitutionProof (acceptsSubst)
open NumberedWindowInternalMatchReductionTargets (OTerm suppliedEdge suppliedMatch)
open NumberedWindowNumeralGraphTargets (inputs)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem edgeSubst {β : Type} (r : Program 3) (x y : OTerm α) (ts : α → OTerm β) :
    (suppliedEdge r x y).subst (fun i => emb (ts i)) = suppliedEdge r (x.subst ts) (y.subst ts) := by
  simp only [suppliedEdge, existsEmbeddedSubst, acceptsSubst, liftTermSubst]
  rfl

private theorem introduceMatch (p r : Program 3) (f u v b cert : OTerm α)
    (app : Derivation body Γ (accepts p f u b)) (edge : Derivation body Γ (accepts r b cert v)) :
    Nonempty (Derivation body Γ (suppliedMatch p r f u v)) := by
  have lifted : Derivation body Γ (suppliedEdge r b v) := by
    apply Derivation.existentialIntroduction (emb cert)
    rw [instantiate, bindEmbedding, acceptsSubst]
    simp only [liftBind, varBind]
    exact edge
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb b)
  rw [instantiate, bindEmbedding, conjunctionSubst, acceptsSubst, edgeSubst]
  simp only [liftBind, varBind]
  exact Derivation.conjunctionIntroduction app lifted

private theorem graphAtNumerals (p : Program 3) (x y k : Nat) :
    Nonempty (Derivation body Γ (programGraph p (numeral (evaluate p (x ::ᵥ y ::ᵥ k ::ᵥ nil)))
      ![numeral x, numeral y, numeral k])) := by
  have hd := NumberedWindowNumeralGraphChecks.exact_NumeralGraph 3 p (x ::ᵥ y ::ᵥ k ::ᵥ nil) body α Γ
  have coords : inputs (α := α) (x ::ᵥ y ::ᵥ k ::ᵥ nil) = ![numeral x, numeral y, numeral k] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i
  rwa [coords] at hd

private theorem accepted (p : Program 3) (x y k : Nat) (h : evaluate p (x ::ᵥ y ::ᵥ k ::ᵥ nil) = 1) :
    Nonempty (Derivation body Γ (accepts p (numeral x) (numeral y) (numeral k))) := by
  have d := graphAtNumerals (body := body) (Γ := Γ) p x y k
  rw [h] at d
  exact d

private theorem rejected (p : Program 3) (x y k : Nat) (h : evaluate p (x ::ᵥ y ::ᵥ k ::ᵥ nil) = 0)
    (d : Derivation body Γ (accepts p (numeral x) (numeral y) (numeral k))) :
    Nonempty (Derivation body Γ ⊥) := by
  have zero := graphAtNumerals (body := body) (Γ := Γ) p x y k
  rw [h] at zero
  obtain ⟨contra⟩ := ID1Completion.InternalControlGraphSupportProof.valueUnique p (suc z) z
    ![numeral x,numeral y,numeral k] ⟨d⟩ zero
  exact ⟨ID1Completion.InternalTagArithmeticSupportProof.sucNeZeroApply contra⟩

theorem exact_ClosedDerivations : NumberedWindowClosedMatchTargets.ClosedDerivations := by
  intro edge app r p hr hp matching body α f g u v w
  let H : Formula α := accepts r (numeral f) (numeral w) (numeral g) ⊓
    accepts p (numeral g) (numeral u) (numeral v)
  have hyp : Derivation body [H] H := Derivation.hypothesis List.mem_cons_self
  suffices d : Nonempty (Derivation body [H] (suppliedMatch p r (numeral f) (numeral u) (numeral v))) by
    exact ⟨Derivation.implicationIntroduction (Classical.choice d)⟩
  cases he : edge f w g with
  | false =>
    obtain ⟨contra⟩ := rejected r f w g (by rw [hr,he]; rfl) (Derivation.conjunctionLeft hyp)
    exact ⟨Derivation.explosion contra⟩
  | true =>
    cases ha : app g u v with
    | false =>
      obtain ⟨contra⟩ := rejected p g u v (by rw [hp,ha]; rfl) (Derivation.conjunctionRight hyp)
      exact ⟨Derivation.explosion contra⟩
    | true =>
      obtain ⟨b,cert,hb,hcert⟩ := matching f g u v w he ha
      apply introduceMatch p r _ _ _ (numeral b) (numeral cert)
      · exact Classical.choice (accepted p f u b (by rw [hp,hb]; rfl))
      · exact Classical.choice (accepted r b cert v (by rw [hr,hcert]; rfl))

#print axioms exact_ClosedDerivations
end LogicLineages.PersistentMarking.NumberedWindowClosedMatchChecks
