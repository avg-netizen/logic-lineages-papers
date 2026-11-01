module
public import LogicLineages.OrdinalComparison.GroundSourceEqualityTargets
public import LogicLineages.OrdinalComparison.SourceScalarMultivariateProof
public import LogicLineages.OrdinalComparison.MultivariateIdentityDecisionProof
public import LogicLineages.OrdinalComparison.WWSourceComparisonProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.GroundSourceEquality
open Source Source.ForwardTranslation
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

attribute [local irreducible] Phi actualCollapse encodedMultivariateIdentity

theorem query_flag_computable : Computable queryEqualityFlag := by
  have hap : Computable (fun q : EncodedQuery => q.2.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.snd)
  have hbp : Computable (fun q : EncodedQuery => q.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have ha0 : Computable (fun q : EncodedQuery => q.2.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.snd)
  have hb0 : Computable (fun q : EncodedQuery => q.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  exact Primrec.and.to_comp.comp
    (Primrec.and.to_comp.comp
      (positiveComparisonPrimitiveRecursive.to_comp.comp hap hbp)
      (positiveComparisonPrimitiveRecursive.to_comp.comp hbp hap))
    (MultivariateIdentityDecision.flag_computable.comp ha0 hb0)

private theorem index_bound {Γ : List Ty} {σ : Ty} (v : Variable Γ σ) :
    SourceTypedPorts.variableIndex v<Γ.length := by
  induction v with
  | here => exact Nat.zero_lt_succ _
  | there v ih => exact Nat.succ_lt_succ ih

private theorem scalar_variables (Γ : List Ty) (s : Scalar (OrdinalComponent Γ)) :
    MultivariateSourceBridge.scalarVariablesBelow
      (fun c => SourceTypedPorts.variableIndex c.2.1) Γ.length s := by
  induction s with
  | one => trivial
  | var x => exact index_bound x.2.1
  | add a b iha ihb => exact ⟨iha,ihb⟩
  | shift c a ih => exact ih

theorem scalar_identity (Γ : List Ty) (hΓ : ∀ σ ∈ Γ, σ=Ty.ground)
    (s t : Scalar (OrdinalComponent Γ)) :
    encodedMultivariateIdentity
      (scalarCode (fun c => SourceTypedPorts.variableIndex c.2.1) s)
      (scalarCode (fun c => SourceTypedPorts.variableIndex c.2.1) t)=true ↔
      ∀ ρ : OrdinalComponent Γ → Nat, (∀ c, 0<ρ c) → s.value ρ=t.value ρ := by
  let index : OrdinalComponent Γ → Nat := fun c => SourceTypedPorts.variableIndex c.2.1
  let E := MultivariateSourceBridge.scalarToMultivariate index s
  let F := MultivariateSourceBridge.scalarToMultivariate index t
  have hE : multivariatePositiveValid Γ.length E :=
    MultivariateSourceBridge.adapter.2.1 _ index Γ.length s (scalar_variables Γ s)
  have hF : multivariatePositiveValid Γ.length F :=
    MultivariateSourceBridge.adapter.2.1 _ index Γ.length t (scalar_variables Γ t)
  have he := MultivariateSourceBridge.adapter.1 _ index s
  have hf := MultivariateSourceBridge.adapter.1 _ index t
  have hi := (MultivariateIdentityDecision.decision.2.2.2 Γ.length E F hE hF).1
  rw [he,hf] at hi
  rw [hi]
  constructor
  · intro h ρ hρ
    obtain ⟨xs,_,hxs⟩ := groundPositiveTupleComplete Γ hΓ ρ hρ
    have hv := h (fun i => xs.getD i 0+1) (by intro i _; omega)
    rw [MultivariateSourceBridge.adapter.2.2 _ index s,
      MultivariateSourceBridge.adapter.2.2 _ index t] at hv
    have hp : (fun c : OrdinalComponent Γ => xs.getD (index c) 0+1)=ρ := funext hxs
    rwa [hp] at hv
  · intro h ρ hρ
    rw [MultivariateSourceBridge.adapter.2.2 _ index s,
      MultivariateSourceBridge.adapter.2.2 _ index t]
    exact h (fun c => ρ (index c)) (fun c => hρ _ (index_bound c.2.1))

private theorem scalar_field {Γ : List Ty} {n : Nat} (v : OrdinalVector Γ n)
    (c : CompiledVector (OrdinalComponent Γ) n) (hc : compileVector v=some c)
    (ρ : OrdinalComponent Γ → Nat) :
    sourceVectorAtValue v ρ 0=(c.scalar.value ρ : Ordinal) := by
  have h := compiledVectorSound Γ n v c hc ρ 0
  simpa [sourceVectorAtValue,ordinalVectorAt,CompiledVector.value] using h.symm

private theorem positive_field {Γ : List Ty} {n : Nat} (v : OrdinalVector Γ n)
    (c : CompiledVector (OrdinalComponent Γ) n) (hc : compileVector v=some c)
    (ρ : OrdinalComponent Γ → Nat) (j : Nat) :
    positiveNoteAt c.positiveNotes j=sourceVectorAtValue v ρ (j+1) := by
  by_cases hj : j<n
  · have h := compiledVectorSound Γ n v c hc ρ (Fin.succ ⟨j,hj⟩)
    simpa [positiveNoteAt,CompiledVector.positiveNotes,List.getD_eq_getElem?_getD,
      List.getElem?_ofFn,hj,sourceVectorAtValue,ordinalVectorAt,Nat.succ_lt_succ hj,
      CompiledVector.value] using h
  · have hn : n≤j := Nat.le_of_not_gt hj
    have hp : c.positiveNotes.length≤j := by simpa [CompiledVector.positiveNotes] using hn
    rw [positiveNoteAt,List.getD_eq_default _ _ hp]
    simp [sourceVectorAtValue,ordinalVectorAt,show ¬j+1<n+1 by omega,zeroNote,denote]

theorem compiled : Targets.GroundCompiledEquality := by
  refine ⟨query_flag_computable,?_⟩
  intro Γ hΓ n m a b ac bc ha hb
  change ((positiveComparison (normalCodes ac.positiveNotes) (normalCodes bc.positiveNotes) &&
    positiveComparison (normalCodes bc.positiveNotes) (normalCodes ac.positiveNotes) &&
    encodedMultivariateIdentity
      (scalarCode (fun c => SourceTypedPorts.variableIndex c.2.1) ac.scalar)
      (scalarCode (fun c => SourceTypedPorts.variableIndex c.2.1) bc.scalar))=true) ↔ _
  rw [Bool.and_eq_true_iff,Bool.and_eq_true_iff,positiveComparisonSourceCorrect,
    positiveComparisonSourceCorrect,scalar_identity Γ hΓ ac.scalar bc.scalar]
  constructor
  · rintro ⟨⟨hpos,hrev⟩,hscalar⟩ ρ hρ j
    cases j with
    | zero =>
      rw [scalar_field a ac ha ρ,scalar_field b bc hb ρ]
      exact congrArg (fun v : Nat => (v : Ordinal)) (hscalar ρ hρ)
    | succ j =>
      rw [← positive_field a ac ha ρ j,← positive_field b bc hb ρ j]
      exact le_antisymm (hpos j) (hrev j)
  · intro h
    have hpositive (j : Nat) : positiveNoteAt ac.positiveNotes j=positiveNoteAt bc.positiveNotes j := by
      rw [positive_field a ac ha (fun _ => 1) j,positive_field b bc hb (fun _ => 1) j]
      exact h (fun _ => 1) (fun _ => Nat.zero_lt_one) (j+1)
    refine ⟨⟨fun j => (hpositive j).le,fun j => (hpositive j).ge⟩,?_⟩
    intro ρ hρ
    have hz := h ρ hρ 0
    rw [scalar_field a ac ha ρ,scalar_field b bc hb ρ] at hz
    exact_mod_cast hz

end LogicLineages.OrdinalComparison.GroundSourceEquality
