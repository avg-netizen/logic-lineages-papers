module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSparseJFoldSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonTargetFoldSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (membershipSubst)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (allEmbeddedSubst liftTermSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowTypeFormulaSubstitutionProof (impSubst)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (tailMember)
open NumberedWindowInternalSparseParsedFoldSyntaxProof (pairAt)
open NumberedWindowInternalLiteralSparseJFoldSyntaxProof (typedAt typedAtSubst memberGraphSubst)
open NumberedWindowInternalLiteralSingletonProgressTargets (singletonMembers)
open NumberedWindowInternalScalarSingletonInductionProof (singletonJ singletonSubst)
open NumberedWindowInternalCertifiedUnionProgressSupportProof (freshKeeps)

def condition {α : Type} (i : Program 1) (n s : OTerm α) : Formula α :=
  (typedAt i s).imp ((singletonMembers s).imp (membership true n))

def motive {α : Type} (i : Program 1) : Formula (α ⊕ Fin 2) :=
  condition i (.var (.inr (0 : Fin 2))) (.var (.inr (1 : Fin 2)))

theorem singletonMembersSubst {α β : Type} (s : OTerm α) (ts : α → OTerm β) :
    (singletonMembers s).subst (fun k => emb (ts k)) = singletonMembers (s.subst ts) := by
  simp only [singletonMembers,allEmbeddedSubst,impSubst,memberGraphSubst,singletonSubst,liftTermSubst] <;> rfl

theorem singletonMembersRename {α β : Type} (s : OTerm α) (j : α → β) :
    (singletonMembers s).relabel j = singletonMembers (s.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (singletonMembers s).subst (fun k => emb (.var (j k))) = _
  rw [singletonMembersSubst,← termRelabelAsSubst]

theorem singletonMembersAt {α : Type} (s q : OTerm α) :
    instantiate ((memberGraph (s.relabel Sum.inl) (.var (.inr (0 : Fin 1)))).imp
      (singletonJ (.var (.inr (0 : Fin 1))))) (emb q) =
      (memberGraph s q).imp (singletonJ q) := by
  simp only [instantiate,bindEmbedding,impSubst,memberGraphSubst,singletonSubst,liftBind,varBind]

theorem conditionSubst {α β : Type} (i : Program 1) (n s : OTerm α) (ts : α → OTerm β) :
    (condition i n s).subst (fun k => emb (ts k)) = condition i (n.subst ts) (s.subst ts) := by
  simp only [condition,impSubst,typedAtSubst,singletonMembersSubst,membershipSubst]

theorem motiveAt {α β : Type} (i : Program 1) (ρ : α → OTerm β) (n s : OTerm β) :
    pairAt (motive (α := α) i) ρ n s = condition i n s := by
  rw [pairAt,motive,conditionSubst] <;> rfl

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem applySingletonMembers (s q : OTerm α)
    (all : Nonempty (Derivation B Γ (singletonMembers s)))
    (occurs : Nonempty (Derivation B Γ (memberGraph s q))) :
    Nonempty (Derivation B Γ (singletonJ q)) := by
  obtain ⟨all⟩ := all
  obtain ⟨occurs⟩ := occurs
  have h := Derivation.universalElimination (emb q) all
  rw [singletonMembersAt] at h
  exact ⟨Derivation.implicationElimination h occurs⟩

/-- The lower formula is supplied only at actual occurrences of the same
scratch tail, transported through the exact observed cons. -/
theorem singletonMembersOfTail (s h st : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph s h st)))
    (all : Nonempty (Derivation B Γ (singletonMembers s))) :
    Nonempty (Derivation B Γ (singletonMembers st)) := by
  let q : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let P := memberGraph (st.relabel Sum.inl) q
  let Δ := P :: Γ.map weaken
  have mapped := renameInto cell Sum.inl Δ (freshKeeps Γ P)
  rw [consGraphRename] at mapped
  have kept := renameInto all Sum.inl Δ (freshKeeps Γ P)
  rw [singletonMembersRename] at kept
  have mem : Nonempty (Derivation B Δ P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have orig := tailMember (s.relabel Sum.inl) (h.relabel Sum.inl) (st.relabel Sum.inl) q mapped mem
  obtain ⟨done⟩ := applySingletonMembers (s.relabel Sum.inl) q kept orig
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction done)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonTargetFoldSyntaxProof
