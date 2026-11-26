module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseParsedFoldProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchMemberTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalScalarSingletonInductionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSparseJFoldSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucSubst zSubst bindEmbedding liftBind varBind)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (programSubst allEmbeddedSubst liftTermSubst)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (membershipSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowTypeFormulaSubstitutionProof (impSubst)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseParsedFoldSyntaxProof (pairAt)
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch)
open NumberedWindowInternalCertifiedUnionStepProof (Pr)
open NumberedWindowInternalScalarSingletonInductionProof (singletonJ)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)

def LiteralEmptyMembership (i : Program 1) (r : Program 3) (c : Nat) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)), Pr (literalData i r) c Γ (membership true (z : OTerm α))

/-- A supplied same-body scalar-to-singleton proof, applied only to an
actual scalar member whose actual carrier checker has accepted. -/
def LiteralScalarSingletonPromotion (i : Program 1) (r : Program 3) (c : Nat) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (q : OTerm α),
    Pr (literalData i r) c Γ (membership false q) →
    Pr (literalData i r) c Γ (unary i (suc z) q) →
    Pr (literalData i r) c Γ (singletonJ q)

def typedAt {α : Type} (i : Program 1) (s : OTerm α) : Formula α :=
  unary (typedScratch i) (suc z) s

def scalarMembers {α : Type} (s : OTerm α) : Formula α :=
  let k : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  allOne ((memberGraph (s.relabel Sum.inl) k).imp (membership false k))

def jCondition {α : Type} (i : Program 1) (n s : OTerm α) : Formula α :=
  (typedAt i s).imp ((scalarMembers s).imp (membership true n))

def jMotive {α : Type} (i : Program 1) : Formula (α ⊕ Fin 2) :=
  jCondition i (.var (.inr (0 : Fin 2))) (.var (.inr (1 : Fin 2)))

theorem memberGraphSubst {α β : Type} (s q : OTerm α) (ts : α → OTerm β) :
    (memberGraph s q).subst (fun k => emb (ts k)) = memberGraph (s.subst ts) (q.subst ts) := by
  unfold memberGraph
  rw [programSubst,sucSubst,zSubst]
  congr 1
  funext k
  exact Fin.cases rfl (Fin.cases rfl (fun u => Fin.elim0 u)) k

theorem typedAtSubst {α β : Type} (i : Program 1) (s : OTerm α) (ts : α → OTerm β) :
    (typedAt i s).subst (fun k => emb (ts k)) = typedAt i (s.subst ts) := by
  unfold typedAt unary
  rw [programSubst,sucSubst,zSubst]
  congr 1
  funext k
  exact Fin.cases rfl (fun u => Fin.elim0 u) k

theorem scalarMembersSubst {α β : Type} (s : OTerm α) (ts : α → OTerm β) :
    (scalarMembers s).subst (fun k => emb (ts k)) = scalarMembers (s.subst ts) := by
  simp only [scalarMembers,allEmbeddedSubst,impSubst,memberGraphSubst,membershipSubst,liftTermSubst] <;> rfl

theorem scalarMembersRename {α β : Type} (s : OTerm α) (j : α → β) :
    (scalarMembers s).relabel j = scalarMembers (s.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (scalarMembers s).subst (fun k => emb (.var (j k))) = _
  rw [scalarMembersSubst,← termRelabelAsSubst]

theorem scalarMembersAt {α : Type} (s q : OTerm α) :
    instantiate ((memberGraph (s.relabel Sum.inl) (.var (.inr (0 : Fin 1)))).imp
      (membership false (.var (.inr (0 : Fin 1))))) (emb q) =
      (memberGraph s q).imp (membership false q) := by
  simp only [instantiate,bindEmbedding,impSubst,memberGraphSubst,membershipSubst,liftBind,varBind]

theorem jConditionSubst {α β : Type} (i : Program 1) (n s : OTerm α) (ts : α → OTerm β) :
    (jCondition i n s).subst (fun k => emb (ts k)) = jCondition i (n.subst ts) (s.subst ts) := by
  simp only [jCondition,impSubst,typedAtSubst,scalarMembersSubst,membershipSubst]

theorem jMotiveAt {α β : Type} (i : Program 1) (ρ : α → OTerm β) (n s : OTerm β) :
    pairAt (jMotive (α := α) i) ρ n s = jCondition i n s := by
  rw [pairAt,jMotive,jConditionSubst] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSparseJFoldSyntaxProof
