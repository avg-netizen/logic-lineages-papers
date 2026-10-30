module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowRawContextBound
public import LogicLineages.ComputabilityKnowledge.GorbowContextTransportProof
public import LogicLineages.ComputabilityKnowledge.GorbowSyntaxValidationProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowRawContextBoundProof
open GorbowSyntax GorbowFreeSupport GorbowRawContextBound

private theorem leFold (xs : List Nat) (z : Nat) : z≤xs.foldl max z := by
  induction xs generalizing z with
  | nil => exact Nat.le_refl z
  | cons a xs ih => exact (le_max_left z a).trans (ih (max z a))
private theorem memberFold (xs : List Nat) (z i : Nat) (hi : i∈xs) : i≤xs.foldl max z := by
  induction xs generalizing z with
  | nil => simp at hi
  | cons a xs ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · exact (le_max_right z i).trans (leFold xs (max z i))
    · exact ih (max z a) hi

theorem tokenBound : Comparators.GorbowRawContextBound.TokenBound := by
  intro raw
  refine ⟨by unfold rawBound; omega,?_⟩
  intro i hi
  have h := memberFold raw 0 i hi
  unfold rawBound
  omega

private theorem termAux (n : Nat) (t : Term n) : ∀ B,
    (∀ i∈GorbowTermPrefixCode.encode t,i<B) → ∀ i∈termSupport t,i<B := by
  induction t with
  | var j =>
    intro B h i hi
    have he : i=j.val := Finset.mem_singleton.mp hi
    subst i
    exact h j.val (by simp [GorbowTermPrefixCode.encode])
  | zero => intro B h i hi; simp [termSupport] at hi
  | succ t ih | universalFunction t ih =>
    intro B h i hi
    exact ih B (fun j hj => h j (List.mem_cons_of_mem _ hj)) i hi
  | add t u ht hu | mul t u ht hu =>
    intro B h i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact ht B (fun j hj => h j (List.mem_cons_of_mem _ (List.mem_append_left _ hj))) i hi
    · exact hu B (fun j hj => h j (List.mem_cons_of_mem _ (List.mem_append_right _ hj))) i hi

private theorem formulaAux (n : Nat) (φ : Formula n) : ∀ B,
    (∀ i∈GorbowFormulaPrefixCode.encode φ,i<B) → ∀ i∈formulaSupport φ,i<B := by
  induction φ with
  | equal t u | knowledge t u =>
    intro B h i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact termAux _ t B (fun j hj => h j (List.mem_cons_of_mem _ (List.mem_append_left _ hj))) i hi
    · exact termAux _ u B (fun j hj => h j (List.mem_cons_of_mem _ (List.mem_append_right _ hj))) i hi
  | universalRelation t | agent t | knowledgeAll t | truth t =>
    intro B h i hi
    exact termAux _ t B (fun j hj => h j (List.mem_cons_of_mem _ hj)) i hi
  | neg φ ih =>
    intro B h i hi
    exact ih B (fun j hj => h j (List.mem_cons_of_mem _ hj)) i hi
  | imp φ ψ hφ hψ | conj φ ψ hφ hψ | disj φ ψ hφ hψ =>
    intro B h i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hφ B (fun j hj => h j (List.mem_cons_of_mem _ (List.mem_append_left _ hj))) i hi
    · exact hψ B (fun j hj => h j (List.mem_cons_of_mem _ (List.mem_append_right _ hj))) i hi
  | all φ ih | ex φ ih =>
    intro B h i hi
    have hs := (GorbowFreeSupportProof.unbindMembership _ i).mp hi
    have hb := ih B (fun j hj => h j (List.mem_cons_of_mem _ hj)) (i+1) hs
    omega

theorem supportBound : Comparators.GorbowRawContextBound.SupportBound :=
  ⟨fun n t => termAux n t _ (tokenBound _).2,fun n φ => formulaAux n φ _ (tokenBound _).2⟩

theorem typedTransport : Comparators.GorbowRawContextBound.TypedTransport := by
  constructor
  · intro n t
    obtain ⟨u,hu⟩ := (GorbowContextTransportProof.exactDomain.1 n _ t).mpr (supportBound.1 n t)
    exact ⟨u,hu,(GorbowContextTransportProof.encodingPreservation.1 _ _ _ _ hu).symm,
      (GorbowContextTransportProof.supportPreservation.1 _ _ _ _ hu).symm⟩
  · intro n φ
    obtain ⟨ψ,hψ⟩ := (GorbowContextTransportProof.exactDomain.2 n _ φ).mpr (supportBound.2 n φ)
    exact ⟨ψ,hψ,(GorbowContextTransportProof.encodingPreservation.2 _ _ _ _ hψ).symm,
      (GorbowContextTransportProof.supportPreservation.2 _ _ _ _ hψ).symm⟩

theorem parserDomain : Comparators.GorbowRawContextBound.ParserDomain := by
  constructor
  · intro raw
    constructor
    · rintro ⟨t,ht⟩
      exact ⟨rawBound raw,t,(GorbowTermPrefixCodeProof.decoderExact _ raw t).mp ht⟩
    · rintro ⟨n,t,rfl⟩
      obtain ⟨u,hu,he,hs⟩ := typedTransport.1 n t
      exact ⟨u,(GorbowTermPrefixCodeProof.decoderExact _ _ u).mpr he.symm⟩
  · intro raw
    constructor
    · rintro ⟨φ,hφ⟩
      exact ⟨rawBound raw,φ,(GorbowFormulaPrefixCodeProof.decoderExact _ raw φ).mp hφ⟩
    · rintro ⟨n,φ,rfl⟩
      obtain ⟨ψ,hψ,he,hs⟩ := typedTransport.2 n φ
      exact ⟨ψ,(GorbowFormulaPrefixCodeProof.decoderExact _ _ ψ).mpr he.symm⟩

theorem exactValidity : Comparators.GorbowRawContextBound.ExactValidity :=
  ⟨fun raw => (GorbowSyntaxValidationProof.exactTypedDomain.1 _ raw).trans (parserDomain.1 raw),
   fun raw => (GorbowSyntaxValidationProof.exactTypedDomain.2 _ raw).trans (parserDomain.2 raw)⟩

private theorem pr_fold : Primrec (fun raw : List Nat => raw.foldl max 0) :=
  Primrec.list_foldl Primrec.id (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
private theorem pr_bound : Primrec rawBound := Primrec.succ.comp pr_fold

theorem uniformPrograms : Comparators.GorbowRawContextBound.UniformPrograms :=
  ⟨pr_bound,GorbowSyntaxValidationProof.uniformPrograms.2.2.2.1.comp (pr_bound.pair Primrec.id),
    GorbowSyntaxValidationProof.uniformPrograms.2.2.2.2.comp (pr_bound.pair Primrec.id)⟩
theorem gorbowRawContextBound : Comparators.GorbowRawContextBound.Target :=
  ⟨tokenBound,supportBound,typedTransport,parserDomain,exactValidity,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowRawContextBoundProof
