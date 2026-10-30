module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowFormulaComposition
public import LogicLineages.ComputabilityKnowledge.GorbowContextSubstitutionProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedBindingProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowFormulaCompositionProof
open GorbowSyntax GorbowFreeSupport GorbowNamedBinding GorbowFormulaSubstitution GorbowFormulaComposition

private theorem shiftSubstitution {m n : Nat} (τ : Fin m → Term n) (t : Term m) :
    GorbowSubstitution.substitute (liftSubstitute τ) (renameTerm Fin.succ t)=
      renameTerm Fin.succ (GorbowSubstitution.substitute τ t) := by
  simp only [renameTerm,GorbowSubstitution.substitute_composition,GorbowSubstitution.substitute,liftSubstitute,Fin.cases_succ]

theorem liftComposition : Comparators.GorbowFormulaComposition.LiftComposition := by
  intro l m n σ τ
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => simpa only [liftSubstitute,Fin.cases_succ] using shiftSubstitution τ (σ i)

private theorem formulaComp (l : Nat) (φ : Formula l) : ∀ m n (σ : Fin l → Term m) (τ : Fin m → Term n),
    substituteFormula τ (substituteFormula σ φ)=
      substituteFormula (fun i => GorbowSubstitution.substitute τ (σ i)) φ := by
  induction φ with
  | equal t u | knowledge t u =>
    intro m n σ τ
    simp only [substituteFormula,GorbowSubstitution.substitute_composition]
  | universalRelation t | agent t | knowledgeAll t | truth t =>
    intro m n σ τ
    simp only [substituteFormula,GorbowSubstitution.substitute_composition]
  | neg φ ih => intro m n σ τ; simp only [substituteFormula,ih m n σ τ]
  | imp φ ψ hφ hψ | conj φ ψ hφ hψ | disj φ ψ hφ hψ =>
    intro m n σ τ
    simp only [substituteFormula,hφ m n σ τ,hψ m n σ τ]
  | all φ ih | ex φ ih =>
    intro m n σ τ
    simp only [substituteFormula,ih (m+1) (n+1) (liftSubstitute σ) (liftSubstitute τ)]
    rw [liftComposition]

theorem composition : Comparators.GorbowFormulaComposition.Composition :=
  fun l m n φ σ τ => formulaComp l φ m n σ τ

private theorem termSelf (n : Nat) (t : Term n) : GorbowContextTransport.term n t=some t := by
  obtain ⟨u,hu⟩ := (GorbowContextTransportProof.exactDomain.1 n n t).mpr (GorbowFreeSupportProof.supportBound.1 n t)
  have he := GorbowContextTransportProof.encodingPreservation.1 n n t u hu
  have ht : t=u := GorbowTermPrefixCodeProof.encodingInjective n he
  simpa only [← ht] using hu
private theorem formulaSelf (n : Nat) (φ : Formula n) : GorbowContextTransport.formula n φ=some φ := by
  obtain ⟨ψ,hψ⟩ := (GorbowContextTransportProof.exactDomain.2 n n φ).mpr (GorbowFreeSupportProof.supportBound.2 n φ)
  have he := GorbowContextTransportProof.encodingPreservation.2 n n φ ψ hψ
  have ht : φ=ψ := GorbowFormulaPrefixCodeProof.encodingInjective n he
  simpa only [← ht] using hψ

theorem occurrenceLocality : Comparators.GorbowFormulaComposition.OccurrenceLocality := by
  intro n m φ σ τ hc
  have h := GorbowContextSubstitutionProof.formulaSubstitution n n m m φ φ (formulaSelf n φ) σ τ
    (by
      intro i j he hi
      have hij : i=j := Fin.ext he
      subst j
      rw [hc i hi]
      exact termSelf m (τ i))
  exact GorbowFormulaPrefixCodeProof.encodingInjective m
    (GorbowContextTransportProof.encodingPreservation.2 m m _ _ h)

theorem namedSyntax : Comparators.GorbowFormulaComposition.NamedSyntax := by
  intro n v φ t
  unfold namedClosedInstance GorbowStandardInstances.instantiate selectVariable
  rw [composition]
  congr 1
  funext i
  by_cases hi : i=v
  · simp [namedClosedDictionary,selectDictionary,hi,GorbowSubstitution.substitute]
  · simp [namedClosedDictionary,selectDictionary,hi,GorbowSubstitution.substitute]

theorem namedSemantics : Comparators.GorbowFormulaComposition.NamedSemantics := by
  intro n v φ hs t I ρ
  rw [namedSyntax]
  exact GorbowNamedBindingProof.closedInstanceCalibration n v φ hs t I ρ

theorem contextInvariance : Comparators.GorbowFormulaComposition.ContextInvariance := by
  intro n m v w hv φ ψ h t
  rw [namedSyntax,namedSyntax]
  rw [(GorbowContextSubstitutionProof.namedCommutation n m v w hv φ ψ h).2.2]

theorem gorbowFormulaComposition : Comparators.GorbowFormulaComposition.Target :=
  ⟨liftComposition,composition,occurrenceLocality,namedSyntax,namedSemantics,contextInvariance⟩
end LogicLineages.ComputabilityKnowledge.GorbowFormulaCompositionProof
