module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJCompleteProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchAllMembersProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRawMembersJProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (carrier membership)
open NumberedWindowInternalAtomicMembershipSyntaxProof (membershipRename)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb sucSubst zSubst bindEmbedding liftBind varBind)
open ID1Completion.InternalComputabilityApplicationSyntaxProof
  (programSubst allEmbeddedSubst liftTermSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof
  (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.SourcePresentation (sourceBody)
open NumberedWindowTypeFormulaSubstitutionProof (impSubst)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectTypedListOpenProof (exact_OpenJRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCoordinateChecks (exact_DomainRules)
open NumberedWindowInternalCertifiedUnionStepProof (Pr)
open NumberedWindowInternalLiteralSparseJFoldSyntaxProof
  (typedAt scalarMembers scalarMembersSubst scalarMembersRename scalarMembersAt)
open NumberedWindowInternalDirectTypedScratchAllMembersTargets (allMembers)
open NumberedWindowInternalDirectTypedScratchAllMembersProof (exact_TypedScratchAllMembers)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open ID1Completion.InternalAccessibilityRulesProof (actualOriginalCarrierExtraction)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)

/-- Every scalar in the actual positively decoded raw multiset is in I.
The literal-carrier premise of the theorem supplies a genuine parser
success, so this formula is not used vacuously on malformed codes. -/
def allRawMembers {α : Type} (raw : OTerm α) : Formula α :=
  let scratch : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  allOne ((unary parser (suc scratch) (raw.relabel Sum.inl)).imp (scalarMembers scratch))

private theorem unaryAtSubst {α β : Type} (p : Program 1) (o x : OTerm α) (ts : α → OTerm β) :
    (unary p o x).subst (fun k => emb (ts k)) = unary p (o.subst ts) (x.subst ts) := by
  unfold unary
  rw [programSubst]
  congr 1
  funext k
  obtain rfl := Fin.eq_zero k
  rfl

private theorem allRawMembersSubst {α β : Type} (raw : OTerm α) (ts : α → OTerm β) :
    (allRawMembers raw).subst (fun k => emb (ts k)) = allRawMembers (raw.subst ts) := by
  simp only [allRawMembers,allEmbeddedSubst,impSubst,unaryAtSubst,sucSubst,
    scalarMembersSubst,liftTermSubst] <;> rfl

private theorem allRawMembersRename {α β : Type} (raw : OTerm α) (j : α → β) :
    (allRawMembers raw).relabel j = allRawMembers (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (allRawMembers raw).subst (fun k => emb (.var (j k))) = _
  rw [allRawMembersSubst,← termRelabelAsSubst]

private theorem instanceAt {α : Type} (raw scratch : OTerm α) :
    instantiate ((unary parser (suc (.var (.inr (0 : Fin 1)))) (raw.relabel Sum.inl)).imp
      (scalarMembers (.var (.inr (0 : Fin 1))))) (emb scratch) =
        ((unary parser (suc scratch) raw).imp (scalarMembers scratch)) := by
  simp only [instantiate,bindEmbedding,impSubst,unaryAtSubst,sucSubst,
    scalarMembersSubst,liftBind,varBind]

private theorem decodedMembers {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw scratch : OTerm α) (all : Nonempty (Derivation B Γ (allRawMembers raw)))
    (decoded : Nonempty (Derivation B Γ (unary parser (suc scratch) raw))) :
    Nonempty (Derivation B Γ (scalarMembers scratch)) := by
  obtain ⟨held⟩ := all
  obtain ⟨parsed⟩ := decoded
  rw [allRawMembers] at held
  have rule := Derivation.universalElimination (emb scratch) held
  rw [instanceAt] at rule
  exact ⟨Derivation.implicationElimination rule parsed⟩

private theorem typedFromMembers (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (scratch : OTerm α)
    (members : Pr (literalData i r) c Γ (scalarMembers scratch)) :
    Pr (literalData i r) c Γ (typedAt i scratch) := by
  let S := literalData i r
  let B := sourceBody S c
  let j : α → α ⊕ Fin 1 := Sum.inl
  let q : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let A := memberGraph (scratch.relabel j) q
  let Δ : List (Formula (α ⊕ Fin 1)) := A :: Γ.map weaken
  have guardAt : Nonempty (Derivation B Δ (unary i (suc z) q)) := by
    have keep (f : Formula α) (h : f ∈ Γ) : f.relabel j ∈ Δ :=
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,h,rfl⟩)
    obtain ⟨inBigger⟩ := renameInto members j Δ keep
    rw [scalarMembersRename,scalarMembers] at inBigger
    have rule := Derivation.universalElimination (emb q) inBigger
    rw [scalarMembersAt] at rule
    have atom := Derivation.implicationElimination rule (Derivation.hypothesis List.mem_cons_self)
    have car := actualOriginalCarrierExtraction S false c _ Δ q ⟨atom⟩
    exact (exact_DomainRules i (jRaw i) r (dCore i r permutation) false c B _ Δ q).1 car
  obtain ⟨guard⟩ := guardAt
  have all : Nonempty (Derivation B Γ (allMembers i scratch)) :=
    ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction guard)⟩
  obtain ⟨both⟩ := exact_TypedScratchAllMembers i B α Γ scratch
  obtain ⟨a⟩ := all
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight both) a⟩

/-- Actual raw-code member introduction: a held J-carrier and I for all
members of its successful literal parse imply J in the same installed
body. No scratch decoder witness, typed fold, split or arithmetic
premise is supplied by the caller. -/
theorem exact_LiteralRawMembersJ (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (raw : OTerm α)
    (typed : Pr (literalData i r) c Γ (carrier (literalData i r) true c raw))
    (available : Pr (literalData i r) c Γ (allRawMembers raw)) :
    Pr (literalData i r) c Γ (membership true raw) := by
  let S := literalData i r
  let B := sourceBody S c
  have opened : Nonempty (Derivation B Γ (unary (jRaw i) (suc z) raw)) :=
    (exact_DomainRules i (jRaw i) r (dCore i r permutation) true c B α Γ raw).1 typed
  apply exact_OpenJRaw i B α Γ raw _ opened
  intro β j Δ scratch keep reports
  rw [membershipRename]
  obtain ⟨all⟩ := renameInto available j Δ keep
  rw [allRawMembersRename,allRawMembers] at all
  have rule := Derivation.universalElimination (emb scratch) all
  rw [instanceAt] at rule
  obtain ⟨decoded⟩ := reports.parsed
  exact NumberedWindowInternalLiteralJCompleteProof.exact_LiteralParsedJ i r c β Δ
    (raw.relabel j) scratch ⟨decoded⟩ reports.typed ⟨Derivation.implicationElimination rule decoded⟩

/-- The original literal parser succeeds. The scratch payload stays
existential in the object calculus. -/
def someRawParse {α : Type} (raw : OTerm α) : Formula α :=
  existsOne (unary parser (suc (.var (.inr (0 : Fin 1)))) (raw.relabel Sum.inl))

/-- The members' actual I derivations themselves supply all scalar typing
on a successfully parsed raw code. A caller needs neither a J-carrier
proof nor a chosen scratch witness. -/
theorem exact_LiteralParsedRawMembersJ (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (raw : OTerm α)
    (good : Pr (literalData i r) c Γ (someRawParse raw))
    (available : Pr (literalData i r) c Γ (allRawMembers raw)) :
    Pr (literalData i r) c Γ (membership true raw) := by
  let S := literalData i r
  let B := sourceBody S c
  let j : α → α ⊕ Fin 1 := Sum.inl
  let scratch : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let A := unary parser (suc scratch) (raw.relabel j)
  let Δ : List (Formula (α ⊕ Fin 1)) := A :: Γ.map weaken
  have keep (f : Formula α) (h : f ∈ Γ) : f.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,h,rfl⟩)
  have held := renameInto available j Δ keep
  rw [allRawMembersRename] at held
  have parsed : Nonempty (Derivation B Δ A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have members := decodedMembers (raw.relabel j) scratch held parsed
  have typed := typedFromMembers i r c _ Δ scratch members
  obtain ⟨out⟩ := NumberedWindowInternalLiteralJCompleteProof.exact_LiteralParsedJ i r c _ Δ
    (raw.relabel j) scratch parsed typed members
  have last : Derivation B Δ (weaken (membership true raw)) := by
    rw [weaken,membershipRename]
    exact out
  obtain ⟨ok⟩ := good
  exact ⟨Derivation.existentialElimination ok last⟩

#print axioms exact_LiteralRawMembersJ
#print axioms exact_LiteralParsedRawMembersJ
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRawMembersJProof
