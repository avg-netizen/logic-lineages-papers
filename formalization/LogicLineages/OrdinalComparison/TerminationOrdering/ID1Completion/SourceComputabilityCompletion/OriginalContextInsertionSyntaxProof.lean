module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationValidityStackAppendSyntaxProof InternalRawListRecursionSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalGraphCompositionSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalListInduction InternalListInductionSyntaxProof
open OriginalContextInsertion

@[simp] theorem lengthRename {alpha beta : Type} (count code : OTerm alpha) (j : alpha → beta) :
    (lengthGraph count code).relabel j = lengthGraph (count.relabel j) (code.relabel j) := by
  simp only [lengthGraph,programRename,consTermRename,emptyRename]

@[simp] theorem lengthSubst {alpha beta : Type} (count code : OTerm alpha) (ts : alpha → OTerm beta) :
    (lengthGraph count code).subst (fun a => emb (ts a)) =
      lengthGraph (count.subst ts) (code.subst ts) := by
  simp only [lengthGraph,programSubst,consTermSubst,emptySubst]

 theorem witnessesSubst {alpha beta : Type}
    (d cutoff gamma extended front suffix inserted : OTerm alpha) (ts : alpha → OTerm beta) :
    (witnesses d cutoff gamma extended front suffix inserted).subst (fun a => emb (ts a)) =
      witnesses (d.subst ts) (cutoff.subst ts) (gamma.subst ts) (extended.subst ts)
        (front.subst ts) (suffix.subst ts) (inserted.subst ts) := by
  simp only [witnesses,conjunctionSubst,lengthSubst,graph2Subst]

 theorem witnessesRename {alpha beta : Type}
    (d cutoff gamma extended front suffix inserted : OTerm alpha) (j : alpha → beta) :
    (witnesses d cutoff gamma extended front suffix inserted).relabel j =
      witnesses (d.relabel j) (cutoff.relabel j) (gamma.relabel j) (extended.relabel j)
        (front.relabel j) (suffix.relabel j) (inserted.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (witnesses d cutoff gamma extended front suffix inserted).subst
    (fun a => emb (.var (j a))) = _
  rw [witnessesSubst]
  simp only [← termRelabelAsSubst]

 theorem blockSubst {alpha beta : Type} {k : Nat} (phi : Formula (alpha ⊕ Fin k))
    (ts : alpha → Term beta) :
    (InternalFiniteBlocks.block phi).subst ts = InternalFiniteBlocks.block
      (phi.subst (Sum.elim (fun a => (ts a).relabel Sum.inl) (fun i => .var (.inr i)))) := by
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst]

 theorem insertSubst {alpha beta : Type} (d cutoff gamma extended : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (Insert d cutoff gamma extended).subst (fun a => emb (ts a)) =
      Insert (d.subst ts) (cutoff.subst ts) (gamma.subst ts) (extended.subst ts) := by
  unfold OriginalContextInsertion.Insert
  rw [blockSubst,liftedEmbedding,witnessesSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem insertRename {alpha beta : Type} (d cutoff gamma extended : OTerm alpha)
    (j : alpha → beta) :
    (Insert d cutoff gamma extended).relabel j =
      Insert (d.relabel j) (cutoff.relabel j) (gamma.relabel j) (extended.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Insert d cutoff gamma extended).subst (fun a => emb (.var (j a))) = _
  rw [insertSubst]
  simp only [← termRelabelAsSubst]

 theorem insertWitness {alpha : Type} (d cutoff gamma extended front suffix inserted : OTerm alpha) :
    (witnesses (d.relabel Sum.inl) (cutoff.relabel Sum.inl)
      (gamma.relabel Sum.inl) (extended.relabel Sum.inl)
      (.var (.inr (0 : Fin 3))) (.var (.inr 1)) (.var (.inr 2))).subst
        (Sum.elim Term.var (fun i => emb (![front,suffix,inserted] i))) =
      witnesses d cutoff gamma extended front suffix inserted := by
  have he : (Sum.elim Term.var (fun i => emb (![front,suffix,inserted] i))) =
      (fun a => emb (Sum.elim Term.var ![front,suffix,inserted] a)) := by
    funext a
    cases a <;> rfl
  rw [he,witnessesSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

 theorem andLeft {p q : Formula alpha} (h : Nonempty (Derivation body Gamma (p ⊓ q))) :
    Nonempty (Derivation body Gamma p) := by
  obtain ⟨h⟩ := h
  exact ⟨Derivation.conjunctionLeft h⟩

 theorem andRight {p q : Formula alpha} (h : Nonempty (Derivation body Gamma (p ⊓ q))) :
    Nonempty (Derivation body Gamma q) := by
  obtain ⟨h⟩ := h
  exact ⟨Derivation.conjunctionRight h⟩

 theorem andIntro {p q : Formula alpha} (hp : Nonempty (Derivation body Gamma p))
    (hq : Nonempty (Derivation body Gamma q)) : Nonempty (Derivation body Gamma (p ⊓ q)) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hq⟩ := hq
  exact ⟨Derivation.conjunctionIntroduction hp hq⟩

 theorem insertIntro (d cutoff gamma extended front suffix inserted : OTerm alpha)
    (h : Nonempty (Derivation body Gamma (witnesses d cutoff gamma extended front suffix inserted))) :
    Nonempty (Derivation body Gamma (Insert d cutoff gamma extended)) := by
  apply InternalFiniteBlocksProof.actualFiniteExistentialIntroduction body alpha 3 Gamma _
    (fun i => emb (![front,suffix,inserted] i))
  rw [insertWitness]
  exact h

 theorem insertCases (d cutoff gamma extended : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Gamma (Insert d cutoff gamma extended)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta))
      (front suffix inserted : OTerm beta),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (witnesses (d.relabel j) (cutoff.relabel j)
        (gamma.relabel j) (extended.relabel j) front suffix inserted)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  let P := witnesses (d.relabel Sum.inl) (cutoff.relabel Sum.inl)
    (gamma.relabel Sum.inl) (extended.relabel Sum.inl)
    (.var (.inr (0 : Fin 3))) (.var (.inr 1)) (.var (.inr 2))
  apply InternalFiniteBlocksProof.actualFiniteExistentialElimination body alpha 3 Gamma P psi h
  exact next (alpha ⊕ Fin 3) Sum.inl (P :: Gamma.map (fun p => p.relabel Sum.inl))
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
