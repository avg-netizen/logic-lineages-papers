module
public import LogicLineages.OrdinalComparison.WWOriginalWeakReplacementTargets
public import LogicLineages.OrdinalComparison.WWOriginalSupportProof
public import LogicLineages.OrdinalComparison.WWOriginalDeltaProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

private theorem weakened_occurs {Γ : List Ty} {σ : Ty} (t : OrdinalExpression Γ) :
    ordinalHeadOccurs (σ := σ)
      (ordinalExpressionRename (fun {_} x => Variable.there x) t) = false := by
  induction t with
  | var c => rcases c with ⟨τ, x, j⟩; rfl
  | zero => rfl
  | one => rfl
  | omega => rfl
  | add f g ihf ihg =>
    change (ordinalHeadOccurs (ordinalExpressionRename (fun {_} x => Variable.there x) f) ||
      ordinalHeadOccurs (ordinalExpressionRename (fun {_} x => Variable.there x) g)) = false
    rw [ihf, ihg]
    rfl
  | emul f g ihf ihg =>
    change (ordinalHeadOccurs (ordinalExpressionRename (fun {_} x => Variable.there x) f) ||
      ordinalHeadOccurs (ordinalExpressionRename (fun {_} x => Variable.there x) g)) = false
    rw [ihf, ihg]
    rfl
  | collapse f g ihf ihg =>
    change (ordinalHeadOccurs (ordinalExpressionRename (fun {_} x => Variable.there x) f) ||
      ordinalHeadOccurs (ordinalExpressionRename (fun {_} x => Variable.there x) g)) = false
    rw [ihf, ihg]
    rfl

private theorem weakened_free {Γ : List Ty} {σ : Ty} (t : OrdinalExpression Γ) :
    ordinalHeadFree (σ := σ)
      (ordinalExpressionRename (fun {_} x => Variable.there x) t) = true := by
  simp only [ordinalHeadFree, weakened_occurs, Bool.not_false]

theorem originalWeakReplacement : Targets.OriginalWeakReplacement := by
  intro Γ σ p
  refine ⟨?_, ?_, ?_⟩
  · exact originalSourceWeakScalar Γ σ p
  · intro i t ht
    obtain ⟨v, hv, gv, wv⟩ := originalPartialWeakAndValid Γ σ p i t ht
    exact ⟨v, hv, fun j => ⟨gv j, weakened_free (v j)⟩⟩
  · intro m h hh
    obtain ⟨v, hv, gv⟩ := originalDeltaValid Γ σ m p h hh
    exact ⟨v, hv, fun j => ⟨gv j, weakened_free (v j)⟩⟩

end LogicLineages.OrdinalComparison.Source.OriginalDomain
