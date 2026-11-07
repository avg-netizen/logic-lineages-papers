module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionAssemblyProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalPositiveUnfoldingSupportProof InternalBetaCoding InternalBetaCodingSyntaxProof
open InternalBetaExtension InternalBetaExtensionSyntaxProof InternalBetaExtensionSupportProof
open InternalBetaExtensionAssemblyProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem extensionOfCodeWith (a b n z c : OTerm α)
    (h : Nonempty (Derivation body Gamma (codeWith (appendRelation a b n z) c (suc n)))) :
    Nonempty (Derivation body Gamma (extension a b n z)) := by
  obtain ⟨h⟩ := h
  let mat : Formula (α ⊕ Fin 1) := codedBelow ((appendRelation a b n z).relabel (Sum.map (Sum.map Sum.inl id) id))
    (c.relabel Sum.inl) (.var (.inr 0)) ((suc n).relabel Sum.inl)
  let Delta := mat :: Gamma.map weaken
  have hm : Nonempty (Derivation body Delta mat) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  rw [show mat = codedBelow
    (appendRelation (a.relabel Sum.inl) (b.relabel Sum.inl) (n.relabel Sum.inl) (z.relabel Sum.inl))
    (c.relabel Sum.inl) (.var (.inr 0)) (suc (n.relabel Sum.inl)) by
      simp only [mat,appendRelationRename,sucRelabel]
    ] at hm
  obtain ⟨he⟩ := codedExtension _ _ _ _ _ _ hm
  apply Nonempty.intro
  apply Derivation.existentialElimination h
  change Derivation body Delta ((extension a b n z).relabel Sum.inl)
  rw [extensionRename]
  exact he

theorem extensionOfCoding (a b n z : OTerm α)
    (h : Nonempty (Derivation body Gamma (coding (appendRelation a b n z) (suc n)))) :
    Nonempty (Derivation body Gamma (extension a b n z)) := by
  obtain ⟨h⟩ := h
  let mat : Formula (α ⊕ Fin 1) := codeWith ((appendRelation a b n z).relabel (Sum.map (Sum.map Sum.inl id) id))
    (.var (.inr 0)) ((suc n).relabel Sum.inl)
  let Delta := mat :: Gamma.map weaken
  have hm : Nonempty (Derivation body Delta mat) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  rw [show mat = codeWith
    (appendRelation (a.relabel Sum.inl) (b.relabel Sum.inl) (n.relabel Sum.inl) (z.relabel Sum.inl))
    (.var (.inr 0)) (suc (n.relabel Sum.inl)) by
      simp only [mat,appendRelationRename,sucRelabel]
    ] at hm
  obtain ⟨he⟩ := extensionOfCodeWith (body := body) (Gamma := Delta)
    (a.relabel Sum.inl) (b.relabel Sum.inl) (n.relabel Sum.inl) (z.relabel Sum.inl) (.var (.inr 0)) hm
  apply Nonempty.intro
  apply Derivation.existentialElimination h
  change Derivation body Delta ((extension a b n z).relabel Sum.inl)
  rw [extensionRename]
  exact he

/-- A genuine internally chosen shared code pair, with no bound or modulus premise. -/
theorem actualBetaSequenceExtension : InternalBetaExtensionTargets.ActualBetaSequenceExtension := by
  intro body α a b n z
  obtain ⟨ha⟩ := appendAvailable (body := body) (Gamma := []) a b n z
  obtain ⟨hc⟩ := InternalBetaCodingProof.actualBoundedBetaCoding body α (suc n) (appendRelation a b n z)
  exact extensionOfCoding a b n z ⟨Derivation.implicationElimination hc ha⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionProof
