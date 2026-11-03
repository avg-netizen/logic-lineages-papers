module
public import LogicLineages.OrdinalComparison.TerminationOrdering.CoherentConstructorLatticeTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.CoherentConstructorLatticeSupportProof
open Source Source.SourceMarkedSyntax FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice
open FiniteQueryPrimitives FiniteQueryPrimitivesSupportProof

theorem argumentRootTypes {Symbol : Type} {arity : Symbol → Nat} {Γ ts : List Ty}
    (K : Ty → Prop) (args : Arguments Symbol arity Γ ts) (h : argumentTypesAllowed K args) : ∀ τ ∈ ts,K τ := by
  induction ts with
  | nil => simp
  | cons σ ts ih =>
      cases args with
      | cons q rest =>
          intro τ ht
          rcases List.mem_cons.mp ht with he | ht
          · subst τ; exact rootType q h.1
          · exact ih rest h.2 τ ht

theorem headDeclarationTypes {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (K : Ty → Prop) (q : MarkedTerm Symbol arity Γ τ) :
    typesAllowed K q → ∀ f ∈ markedHeads q,∀ υ ∈ headArguments arity f,K υ := by
  induction q using MarkedTerm.rec
    (motive_2 := fun Γ ts args => argumentTypesAllowed K args → ∀ f ∈ argumentHeads args,∀ υ ∈ headArguments arity f,K υ) with
  | var v => intro hk f hf; cases hf
  | lam body ih => intro hk; exact ih hk.2.2
  | ordinary hd base ih =>
      intro hk f hf
      rcases List.mem_cons.mp hf with he | hf
      · subst f; exact argumentRootTypes K base hk.2
      · exact ih hk.2 f hf
  | marked hd out base ts extras ihb ihe =>
      intro hk f hf
      rcases List.mem_cons.mp hf with he | hf
      · subst f; exact argumentRootTypes K base hk.2.1
      · rcases List.mem_append.mp hf with hb | he
        · exact ihb hk.2.1 f hb
        · exact ihe hk.2.2 f he
  | nil =>
      rename_i hk f hf υ hυ
      cases hf
  | cons q rest ihq ihr =>
      rename_i hk f hf υ hυ
      rcases List.mem_append.mp hf with hq | hr
      · exact ihq hk.1 f hq υ hυ
      · exact ihr hk.2 f hr υ hυ

theorem headBaseTypes : CoherentConstructorLatticeTargets.HeadBaseTypes := by
  intro Symbol inst arity I f
  have hk := (FiniteQueryPrimitivesProof.initialFrame Symbol arity I.context I.sourceType I.targetType I.source I.target).2.1
  exact headDeclarationTypes (fun τ => τ ∈ types I) (embed I.source) hk f.val f.property

end LogicLineages.OrdinalComparison.TerminationOrdering.CoherentConstructorLatticeSupportProof
