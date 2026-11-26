module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTapeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionBlockBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalBinderTransportSyntaxProof (termRelabelSubst termSubstVar)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialIntroduction actualFiniteExistentialElimination)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucRelabel zRelabel sucSubst zSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (unarySubst graph5Subst graph5Rename)
open NumberedWindowInternalSparsePositiveHeadDecompositionBlockBindingProof (blockRename)
open NumberedWindowInternalSparseAddressPositiveOpenTargets

theorem addressReportRename {α β : Type} (addr c t k : OTerm α) (j : α → β) :
    (addressReport addr c t k).relabel j =
      addressReport (addr.relabel j) (c.relabel j) (t.relabel j) (k.relabel j) := by
  simp only [addressReport,conjunctionRename,unaryRename,sucRelabel,zRelabel]

private theorem addressReportSubst {α β : Type} (addr c t k : OTerm α) (ts : α → OTerm β) :
    (addressReport addr c t k).subst (fun a => emb (ts a)) =
      addressReport (addr.subst ts) (c.subst ts) (t.subst ts) (k.subst ts) := by
  simp only [addressReport,conjunctionSubst,unarySubst,sucSubst,zSubst]

theorem dataRename {α β : Type} (cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (left cert right c t p q : OTerm α) (j : α → β) :
    (witnessData cv tv raw least left cert right c t p q).relabel j =
      witnessData cv tv raw least (left.relabel j) (cert.relabel j) (right.relabel j) (c.relabel j)
        (t.relabel j) (p.relabel j) (q.relabel j) := by
  simp only [witnessData,conjunctionRename,addressReportRename,unaryRename,graph5Rename,sucRelabel,zRelabel]

theorem reportRename {α β : Type} (cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (left cert right : OTerm α) (j : α → β) :
    (someAddressPositive cv tv raw least left cert right).relabel j =
      someAddressPositive cv tv raw least (left.relabel j) (cert.relabel j) (right.relabel j) := by
  simp only [someAddressPositive,blockRename,witnessRow,dataRename,Term.relabel_relabel,Term.relabel] <;> rfl

private theorem witnessLift {α : Type} (n : OTerm α) (xs : Fin 4 → OTerm α) :
    (n.relabel Sum.inl).subst (Sum.elim Term.var xs) = n := by
  rw [termRelabelSubst]
  exact termSubstVar n

private abbrev values {α : Type} (c t p q : OTerm α) : Fin 4 → OTerm α := ![c,t,p,q]

private theorem rowWitness {α : Type} (cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (left cert right c t p q : OTerm α) :
    (witnessRow cv tv raw least left cert right).subst
        (Sum.elim Term.var (fun i => emb (values c t p q i))) =
      witnessData cv tv raw least left cert right c t p q := by
  let xs := values c t p q
  have h : (Sum.elim Term.var (fun i => emb (xs i))) = (fun a => emb (Sum.elim Term.var xs a)) := by
    funext a
    cases a <;> rfl
  change (witnessRow cv tv raw least left cert right).subst (Sum.elim Term.var (fun i => emb (xs i))) = _
  rw [h]
  simp only [witnessRow,witnessData,conjunctionSubst,addressReportSubst,unarySubst,graph5Subst,
    witnessLift,sucSubst,zSubst,Term.subst,Sum.elim_inr] <;> rfl

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem supply (cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (left cert right c t p q : OTerm α)
    (known : Nonempty (Derivation body Γ (witnessData cv tv raw least left cert right c t p q))) :
    Nonempty (Derivation body Γ (someAddressPositive cv tv raw least left cert right)) := by
  apply actualFiniteExistentialIntroduction body α 4 Γ (witnessRow cv tv raw least left cert right)
    (fun i => emb (values c t p q i))
  rw [rowWitness]
  exact known

theorem reportsCases (cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (left cert right : OTerm α) (goal : Formula α)
    (known : Nonempty (Derivation body Γ (someAddressPositive cv tv raw least left cert right)))
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (c t p q : OTerm β),
      (∀ a ∈ Γ, a.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (witnessData cv tv raw least (left.relabel j) (cert.relabel j) (right.relabel j) c t p q)) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  let j : α → α ⊕ Fin 4 := Sum.inl
  let row := witnessRow cv tv raw least left cert right
  let Δ := row :: Γ.map (fun p => p.relabel j)
  apply actualFiniteExistentialElimination body α 4 Γ row goal known
  have hJ (p : Formula α) (hp : p ∈ Γ) : p.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have r : Nonempty (Derivation body Δ row) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact k (α ⊕ Fin 4) j Δ (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) hJ r

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
