module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCodingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaUniquenessProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalCoprimeMultiple InternalCoprimeMultipleSyntaxProof InternalCoprimeMultipleBoundedProof
open InternalRelationalCRT InternalRelationalCRTSyntaxProof InternalRelationalCRTChoiceProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionSyntaxProof
open InternalPositiveUnfoldingSupportProof InternalLeastNumberSyntaxProof InternalOriginalOrderSyntaxProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalDerivationRenamingSyntaxProof InternalBetaTotalitySyntaxProof InternalBetaDivisionSyntaxProof
open InternalBetaCoding InternalBetaCodingSyntaxProof InternalBetaExtension
open InternalTermSubstitutionProof InternalQuotientComparisonSyntaxProof InternalBetaBoundaryProof
open InternalAdditionLawsProof

theorem impRename {α β : Type} (p q : Formula α) (j : α → β) :
    (p.imp q).relabel j = (p.relabel j).imp (q.relabel j) := rfl

theorem sameAtRename {α β : Type} (a b c d i : OTerm α) (j : α → β) :
    (sameAt a b c d i).relabel j = sameAt (a.relabel j) (b.relabel j)
      (c.relabel j) (d.relabel j) (i.relabel j) := by
  unfold sameAt
  rw [actualUniversalRenaming,infRename]
  simp only [impRename,beta,betaRename,Term.relabel_relabel,mapInl,varMap]

theorem sameAtSubst {α β : Type} (a b c d i : OTerm α) (ts : α → OTerm β) :
    (sameAt a b c d i).subst (fun x => emb (ts x)) =
      sameAt (a.subst ts) (b.subst ts) (c.subst ts) (d.subst ts) (i.subst ts) := by
  unfold sameAt
  rw [actualUniversalSubstitution,liftEmbedding]
  simp only [infSubst,impSubst,beta,betaSubst,liftSubst]
  rfl

theorem sameBelowRename {α β : Type} (a b c d n : OTerm α) (j : α → β) :
    (sameBelow a b c d n).relabel j = sameBelow (a.relabel j) (b.relabel j)
      (c.relabel j) (d.relabel j) (n.relabel j) := by
  unfold sameBelow
  rw [boundedRename,sameAtRename]
  simp only [Term.relabel_relabel,mapInl,varMap]

theorem sameBelowSubst {α β : Type} (a b c d n : OTerm α) (ts : α → OTerm β) :
    (sameBelow a b c d n).subst (fun x => emb (ts x)) =
      sameBelow (a.subst ts) (b.subst ts) (c.subst ts) (d.subst ts) (n.subst ts) := by
  unfold sameBelow
  rw [boundedSubst,sameAtSubst]
  simp only [liftSubst]
  rfl

theorem extensionMatrixRename {α β : Type} (a b n z c d : OTerm α) (j : α → β) :
    (extensionMatrix a b n z c d).relabel j = extensionMatrix (a.relabel j) (b.relabel j)
      (n.relabel j) (z.relabel j) (c.relabel j) (d.relabel j) := by
  rw [extensionMatrix,infRename,sameBelowRename,beta,betaRename]
  rfl

theorem extensionMatrixSubst {α β : Type} (a b n z c d : OTerm α) (ts : α → OTerm β) :
    (extensionMatrix a b n z c d).subst (fun x => emb (ts x)) =
      extensionMatrix (a.subst ts) (b.subst ts) (n.subst ts) (z.subst ts) (c.subst ts) (d.subst ts) := by
  rw [extensionMatrix,infSubst,sameBelowSubst,beta,betaSubst]
  rfl

theorem extensionWithRename {α β : Type} (a b n z c : OTerm α) (j : α → β) :
    (extensionWith a b n z c).relabel j = extensionWith (a.relabel j) (b.relabel j)
      (n.relabel j) (z.relabel j) (c.relabel j) := by
  rw [extensionWith,existsRename,extensionMatrixRename]
  simp only [extensionWith,Term.relabel_relabel,mapInl,varMap]

theorem extensionWithSubst {α β : Type} (a b n z c : OTerm α) (ts : α → OTerm β) :
    (extensionWith a b n z c).subst (fun x => emb (ts x)) =
      extensionWith (a.subst ts) (b.subst ts) (n.subst ts) (z.subst ts) (c.subst ts) := by
  rw [extensionWith,existsSubst,liftEmbedding,extensionMatrixSubst]
  simp only [extensionWith,liftSubst]
  rfl

theorem extensionRename {α β : Type} (a b n z : OTerm α) (j : α → β) :
    (extension a b n z).relabel j = extension (a.relabel j) (b.relabel j) (n.relabel j) (z.relabel j) := by
  rw [extension,existsRename,extensionWithRename]
  simp only [extension,Term.relabel_relabel,mapInl,varMap]

/-- The relation used only to construct the code. It is not a premise of the target. -/
def point {α : Type} (a b n z i r : OTerm α) : Formula α :=
  (ltF i n ⊓ beta a b i r) ⊔ (eqn i n ⊓ eqn r z)

def residueRelation {α : Type} (a b n z i : OTerm α) : Formula (α ⊕ Fin 1) :=
  point (a.relabel Sum.inl) (b.relabel Sum.inl) (n.relabel Sum.inl) (z.relabel Sum.inl)
    (i.relabel Sum.inl) (.var (.inr 0))

def appendRelation {α : Type} (a b n z : OTerm α) : Formula ((α ⊕ Fin 1) ⊕ Fin 1) :=
  residueRelation (a.relabel Sum.inl) (b.relabel Sum.inl) (n.relabel Sum.inl)
    (z.relabel Sum.inl) (.var (.inr 0))

theorem pointRename {α β : Type} (a b n z i r : OTerm α) (j : α → β) :
    (point a b n z i r).relabel j = point (a.relabel j) (b.relabel j) (n.relabel j)
      (z.relabel j) (i.relabel j) (r.relabel j) := by
  unfold point
  rw [supRename,infRename,infRename,orderRename,beta,betaRename,eqnRelabel,eqnRelabel]

theorem pointSubst {α β : Type} (a b n z i r : OTerm α) (ts : α → OTerm β) :
    (point a b n z i r).subst (fun x => emb (ts x)) = point (a.subst ts) (b.subst ts)
      (n.subst ts) (z.subst ts) (i.subst ts) (r.subst ts) := by
  change ((ltF i n).subst _ ⊓ (beta a b i r).subst _) ⊔
    ((eqn i n).subst _ ⊓ (eqn r z).subst _) = _
  rw [orderSubst,beta,betaSubst,eqnSubst,eqnSubst]
  rfl

theorem residueRelationRename {α β : Type} (a b n z i : OTerm α) (j : α → β) :
    (residueRelation a b n z i).relabel (Sum.map j id) = residueRelation
      (a.relabel j) (b.relabel j) (n.relabel j) (z.relabel j) (i.relabel j) := by
  rw [residueRelation,pointRename]
  simp only [residueRelation,Term.relabel_relabel,mapInl,varMap]

theorem residueRelationInstantiate {α : Type} (a b n z i r : OTerm α) :
    instantiate (residueRelation a b n z i) (emb r) = point a b n z i r := by
  rw [residueRelation,instantiate,bindEmbedding,pointSubst]
  simp only [liftBind,varBind]

theorem appendRelationRename {α β : Type} (a b n z : OTerm α) (j : α → β) :
    (appendRelation a b n z).relabel (Sum.map (Sum.map j id) id) =
      appendRelation (a.relabel j) (b.relabel j) (n.relabel j) (z.relabel j) := by
  rw [appendRelation,residueRelationRename]
  simp only [appendRelation,Term.relabel_relabel,mapInl,varMap]

theorem atAppendIndex {α : Type} (a b n z i : OTerm α) :
    (appendRelation a b n z).subst (fun x => emb (liftTerms (bindTerm i) x)) =
      residueRelation a b n z i := by
  unfold appendRelation residueRelation
  rw [pointSubst]
  simp only [liftSubst,liftBind,varBind]
  rfl

theorem availableAtAppend {α : Type} (a b n z i : OTerm α) :
    instantiate (existsOne (appendRelation a b n z)) (emb i) =
      existsOne (residueRelation a b n z i) := by
  rw [instantiate,bindEmbedding,existsSubst,liftEmbedding,atAppendIndex]

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
theorem extensionIntroduction (a b n z c d : OTerm α)
    (h : Nonempty (Derivation body Gamma (extensionMatrix a b n z c d))) :
    Nonempty (Derivation body Gamma (extension a b n z)) := by
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb c)
  rw [instantiate,bindEmbedding,extensionWithSubst]
  simp only [liftBind,varBind]
  apply Derivation.existentialIntroduction (emb d)
  rw [instantiate,bindEmbedding,extensionMatrixSubst]
  simpa only [liftBind,varBind] using h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionSyntaxProof
