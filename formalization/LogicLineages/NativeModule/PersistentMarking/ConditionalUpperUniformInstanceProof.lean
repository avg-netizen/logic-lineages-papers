module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof

/-! Step (i) of the uniform bridge: ∀-elimination of the all-terms sentence at a numeral.  The
sentence is literally `allOne (carrier d false c v ⟶ membership false v)` for the bound object
variable v; the instance is computed with the accepted substitution lemmas of the internal line
(`formulaSubstComposition`, `embedSubst`, `numeralSubst`, `membershipSubst`). -/

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalUpperUniformInstanceProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators PositiveArithmeticTransforms SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules ID1Completion.SourcePresentation
open ID1Completion.InternalAccessibilityRulesSyntaxProof ID1Completion.InternalTermSubstitutionSyntaxProof
open ID1Completion.InternalGraphCompositionSyntaxProof
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm emb bindEmbedding bindTerm varBind)
open ConditionalUpperUniformTargets

theorem carrierSubst {α β : Type} (data : Data) (odd : Bool) (context : Nat)
    (x : OTerm α) (ts : α → OTerm β) :
    (carrier data odd context x).subst (fun a => emb (ts a)) = carrier data odd context (x.subst ts) := by
  unfold carrier
  rw [← embedSubst, formulaSubstComposition]
  congr 1
  congr 1
  funext i
  exact Fin.cases (numeralSubst context ts) (Fin.cases rfl (fun j => Fin.elim0 j)) i

theorem allTermsShape (d : Data) (c : Nat) :
    allTermsFormula d c =
      allOne ((carrier d false c (.var (.inr (0 : Fin 1)) : OTerm (Empty ⊕ Fin 1))).imp
        (membership false (.var (.inr (0 : Fin 1)) : OTerm (Empty ⊕ Fin 1)))) := rfl

theorem allTermsInstanceFormula (d : Data) (c : Nat) (y : OTerm Empty) :
    instantiate ((carrier d false c (.var (.inr (0 : Fin 1)) : OTerm (Empty ⊕ Fin 1))).imp
        (membership false (.var (.inr (0 : Fin 1)) : OTerm (Empty ⊕ Fin 1)))) (emb y) =
      (carrier d false c y).imp (membership false y) := by
  unfold instantiate
  rw [bindEmbedding]
  change ((carrier d false c (.var (.inr (0 : Fin 1)))).subst (fun a => emb (bindTerm y a))).imp
      ((membership false (.var (.inr (0 : Fin 1)))).subst (fun a => emb (bindTerm y a))) = _
  rw [carrierSubst, membershipSubst, varBind]

theorem exact_AllTermsInstance : AllTermsInstance := by
  intro B d c x ⟨h⟩
  rw [allTermsShape] at h
  have e := Derivation.universalElimination (emb (numeral x)) h
  rw [allTermsInstanceFormula] at e
  exact ⟨e⟩

#print axioms exact_AllTermsInstance

end LogicLineages.PersistentMarking.ConditionalUpperUniformInstanceProof
