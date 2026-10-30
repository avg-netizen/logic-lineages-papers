module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedRevisionComposition
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionProof
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaCompositionProof
public import LogicLineages.ComputabilityKnowledge.GorbowStandardInstancesProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionCompositionProof
open GorbowSyntax GorbowFreeSupport GorbowNamedBinding GorbowFormulaComposition GorbowStandardInstances
open GorbowSortedSyntaxCode GorbowSortedRevision

private theorem truthNext (g : Ground) (initial : Extension) (k : Nat) (σ : Sentence) :
    (truthSentence σ).realize (stage g initial (k+1)) Fin.elim0 ↔ σ.realize (stage g initial k) Fin.elim0 :=
  (GorbowSortedRevisionProof.successorCalibration g initial k σ).1

theorem booleanTruth : Comparators.GorbowSortedRevisionComposition.BooleanTruth := by
  intro g initial k σ τ
  simp [truthNext,Formula.realize]

private theorem allInstances (n : Nat) (v : Fin n) (φ : Formula n) (hs : formulaSupport φ={v.val}) (I : Interpretation) (ρ : Fin n → Nat) :
    (∀ x,φ.realize I (assignAt ρ v x)) ↔ ∀ t : Term 0,(namedClosedInstance v φ t).realize I Fin.elim0 := by
  constructor
  · intro h t
    exact (GorbowFormulaCompositionProof.namedSemantics n v φ hs t I ρ).mpr (h (t.realize I Fin.elim0))
  · intro h x
    have hx := (GorbowFormulaCompositionProof.namedSemantics n v φ hs (Term.numeral x) I ρ).mp (h (Term.numeral x))
    simpa only [numeral_realize] using hx

private theorem exInstances (n : Nat) (v : Fin n) (φ : Formula n) (hs : formulaSupport φ={v.val}) (I : Interpretation) (ρ : Fin n → Nat) :
    (∃ x,φ.realize I (assignAt ρ v x)) ↔ ∃ t : Term 0,(namedClosedInstance v φ t).realize I Fin.elim0 := by
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨Term.numeral x,(GorbowFormulaCompositionProof.namedSemantics n v φ hs _ I ρ).mpr ?_⟩
    simpa only [numeral_realize] using hx
  · rintro ⟨t,ht⟩
    exact ⟨t.realize I Fin.elim0,(GorbowFormulaCompositionProof.namedSemantics n v φ hs t I ρ).mp ht⟩

theorem namedQuantifiers : Comparators.GorbowSortedRevisionComposition.NamedQuantifiers := by
  intro n v φ hs
  obtain ⟨σ,τ,hσ,hτ,heσ,heτ,hsem⟩ := GorbowContextTransportProof.namedClosure n v φ hs
  refine ⟨σ,τ,congrArg (fun raw => tagFormula (GorbowCodeConstructors.number raw)) heσ,
    congrArg (fun raw => tagFormula (GorbowCodeConstructors.number raw)) heτ,?_⟩
  intro g initial k
  let ρ : Fin n → Nat := fun _ => 0
  constructor
  · simp only [truthNext]
    exact (hsem (stage g initial k) ρ).1.trans (allInstances n v φ hs (stage g initial k) ρ)
  constructor
  · simp only [truthNext]
    exact (hsem (stage g initial k) ρ).2.trans (exInstances n v φ hs (stage g initial k) ρ)
  · intro a ha h
    have ha0 : a=0 := ha
    apply ((GorbowSortedRevisionProof.successorCalibration g initial k σ).2.2 a).mpr
    refine ⟨ha0,(hsem (stage g initial k) ρ).1.mpr ?_⟩
    intro x
    have hx := h (Term.numeral x) (GorbowStandardInstancesProof.arithmeticNumerals 0 x)
    have hv := ((GorbowSortedRevisionProof.successorCalibration g initial k (namedClosedInstance v φ (Term.numeral x))).2.2 a).mp hx
    have he := (GorbowFormulaCompositionProof.namedSemantics n v φ hs (Term.numeral x) (stage g initial k) ρ).mp hv.2
    simpa only [numeral_realize] using he

theorem gorbowSortedRevisionComposition : Comparators.GorbowSortedRevisionComposition.Target :=
  ⟨booleanTruth,namedQuantifiers⟩
end LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionCompositionProof
