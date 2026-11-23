module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAllQueriesTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAgreementBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountConverseProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn emb bindEmbedding liftBind varBind sucSubst zSubst sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue compositionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalApplicationCertificateConstructorsSupportProof (binaryValue)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalRawListRecursion (recGraph)
open ID1Completion.InternalRawListRecursionProof (consValue nilValue)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalListInduction (atCode atIndex constructorBody constructors premises)
open ID1Completion.InternalListInductionProof (actualOriginalListInductionAtCode)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransport (constant sameOf)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalLiteralCount
open NumberedWindowInternalLiteralCountSupportedTargets (accepted)
open NumberedWindowInternalLiteralCountSupportedSyntaxProof (acceptedRename)
open NumberedWindowInternalLiteralCountAllQueriesTargets (agreement)
open NumberedWindowInternalLiteralCountAgreementBindingProof (agreementRename agreementApply)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem tapeThree (c l r : OTerm α) :
    (![c,l,r] : Fin 3 → OTerm α) = Fin.cons c (![l,r] : Fin 2 → OTerm α) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q))) i

private theorem tapeFour (h a l r : OTerm α) :
    (![h,a,l,r] : Fin 4 → OTerm α) = Fin.cons h (Fin.cons a (![l,r] : Fin 2 → OTerm α)) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)))) i

private theorem foldNil (l r : OTerm α) :
    Nonempty (Derivation B Γ (accepted z l r)) := by
  simpa only [accepted,tapeThree,recGraph,allCounts] using
    (nilValue (constant 2 1) step (suc z) ![l,r]
      (constantValue (body := B) (Delta := Γ) 1 ![l,r]))

private theorem stepFromAgreement (head l r lc rc : OTerm α)
    (agree : Nonempty (Derivation B Γ (agreement l r)))
    (lcPay : Nonempty (Derivation B Γ (programGraph entryCount lc ![l,head])))
    (rcPay : Nonempty (Derivation B Γ (programGraph entryCount rc ![r,head]))) :
    Nonempty (Derivation B Γ (programGraph step (suc z) ![head,suc z,l,r])) := by
  let xs : Fin 4 → OTerm α := ![head,suc z,l,r]
  have le : Nonempty (Derivation B Γ (programGraph leftCount lc xs)) :=
    binaryValue entryCount (.projection 2) (.projection 0) lc l head xs
      lcPay (projectionValue 2 xs) (projectionValue 0 xs)
  have re : Nonempty (Derivation B Γ (programGraph rightCount rc xs)) :=
    binaryValue entryCount (.projection 3) (.projection 0) rc r head xs
      rcPay (projectionValue 3 xs) (projectionValue 0 xs)
  have e := agreementApply l r head lc rc agree lcPay rcPay
  have test := binaryValue equalityTest leftCount rightCount (suc z) lc rc xs
    (equalityOfEqual lc rc e) le re
  exact successorBranchIntro (sameOf leftCount rightCount) (constant 4 0) (.projection 1)
    (suc z) z xs test (projectionValue 1 xs)

private theorem foldCons (c h t l r : OTerm α)
    (agree : Nonempty (Derivation B Γ (agreement l r)))
    (cell : Nonempty (Derivation B Γ (consGraph c h t)))
    (tail : Nonempty (Derivation B Γ (accepted t l r))) :
    Nonempty (Derivation B Γ (accepted c l r)) := by
  apply programCases entryCount ![l,h] (accepted c l r)
  intro β j Δ lc keep lcPay
  rw [binaryInputsRename] at lcPay
  rw [acceptedRename]
  have a' := renameInto agree j Δ keep
  have c' := renameInto cell j Δ keep
  have t' := renameInto tail j Δ keep
  rw [agreementRename] at a'
  rw [consGraphRename] at c'
  rw [acceptedRename] at t'
  let c₂ := c.relabel j
  let h₂ := h.relabel j
  let t₂ := t.relabel j
  let l₂ := l.relabel j
  let r₂ := r.relabel j
  apply programCases entryCount ![r₂,h₂] (accepted c₂ l₂ r₂)
  intro γ k Ω rc keep' rcPay
  rw [binaryInputsRename] at rcPay
  rw [acceptedRename]
  have a'' := renameInto a' k Ω keep'
  have c'' := renameInto c' k Ω keep'
  have t'' := renameInto t' k Ω keep'
  rw [agreementRename] at a''
  rw [consGraphRename] at c''
  rw [acceptedRename] at t''
  let c₃ := c₂.relabel k
  let h₃ := h₂.relabel k
  let t₃ := t₂.relabel k
  let l₃ := l₂.relabel k
  let r₃ := r₂.relabel k
  have tailGraph : Nonempty (Derivation B Ω (recGraph (constant 2 1) step (suc z) t₃ ![l₃,r₃])) := by
    simpa only [accepted,tapeThree,recGraph,allCounts,c₃,t₃,l₃,r₃,c₂,t₂,l₂,r₂] using t''
  have selected := stepFromAgreement h₃ l₃ r₃ (lc.relabel k) rc a''
    (renamePair entryCount lc l₂ h₂ lcPay k keep') rcPay
  have out := consValue (constant 2 1) step c₃ h₃ t₃ (suc z) (suc z) ![l₃,r₃] c'' tailGraph
    (by simpa only [tapeFour] using selected)
  simpa only [accepted,tapeThree,recGraph,allCounts,c₃,l₃,r₃,c₂,l₂,r₂] using out

private def motive (l r : OTerm α) : Formula (α ⊕ Fin 1) :=
  accepted (.var (.inr 0)) (l.relabel Sum.inl) (r.relabel Sum.inl)

private theorem formSubst {β : Type} (c l r : OTerm α) (σ : α → OTerm β) :
    (accepted c l r).subst (fun a => emb (σ a)) =
      accepted (c.subst σ) (l.subst σ) (r.subst σ) := by
  have tape : (fun i : Fin 3 => ((![c,l,r] : Fin 3 → OTerm α) i).subst σ) =
      ![c.subst σ,l.subst σ,r.subst σ] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i
  simp only [accepted,programSubst,tape,sucSubst,zSubst]

private theorem motiveCode (c l r : OTerm α) :
    atCode (motive l r) c = accepted c l r := by
  rw [atCode,instantiate,bindEmbedding]
  unfold motive
  rw [formSubst]
  simp only [liftBind,varBind]

private theorem motiveIndex (l r : OTerm α) (i : Fin 3) :
    atIndex (motive l r) i =
      accepted (.var (.inr i)) (l.relabel Sum.inl) (r.relabel Sum.inl) := by
  unfold atIndex motive
  rw [acceptedRename]
  simp only [Term.relabel_relabel,Term.relabel] <;> rfl

private theorem constructorLaw (l r : OTerm α)
    (agree : Nonempty (Derivation B Γ (agreement l r))) :
    Nonempty (Derivation B Γ (constructors (motive l r))) := by
  apply actualFiniteUniversalIntroduction B α 3 Γ (constructorBody (motive l r))
  let j : α → α ⊕ Fin 3 := Sum.inl
  let c : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let h : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let t : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let C := consGraph c h t
  let I := accepted t (l.relabel j) (r.relabel j)
  let Δ := I :: C :: Γ.map (fun f => f.relabel j)
  change Nonempty (Derivation B (Γ.map (fun f => f.relabel j))
    (C.imp ((atIndex (motive l r) 2).imp (atIndex (motive l r) 0))))
  simp only [motiveIndex]
  have keep : ∀ f ∈ Γ, f.relabel j ∈ Δ := by
    intro f hf
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
  have report := renameInto agree j Δ keep
  rw [agreementRename] at report
  obtain ⟨d⟩ := foldCons (B := B) (Γ := Δ) c h t (l.relabel j) (r.relabel j) report
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩

private theorem foldFromAgreement (c l r : OTerm α)
    (agree : Nonempty (Derivation B Γ (agreement l r))) :
    Nonempty (Derivation B Γ (accepted c l r)) := by
  have bs : Nonempty (Derivation B Γ (atCode (motive l r) z)) := by
    rw [motiveCode]
    exact foldNil l r
  obtain ⟨d⟩ := bs
  obtain ⟨k⟩ := constructorLaw (B := B) (Γ := Γ) l r agree
  have hw : Nonempty (Derivation B Γ (premises (motive l r))) :=
    ⟨Derivation.conjunctionIntroduction d k⟩
  have done := actualOriginalListInductionAtCode B α Γ (motive l r) c hw
  rw [motiveCode] at done
  exact done

/-- Internal all-needle agreement constructs acceptance of the same actual
selected observer; no metalevel query-family premise enters the fold. -/
theorem exact_LiteralAgreementAccept (B : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (left right : OTerm α)
    (held : Nonempty (Derivation B Γ (agreement left right))) :
    Nonempty (Derivation B Γ (programGraph permutation (suc z) ![left,right])) := by
  apply programCases append ![left,right] _
  intro β j Δ joined keep ap
  rw [binaryInputsRename] at ap
  simp only [programRename,binaryInputsRename,sucRelabel,zRelabel]
  have a := renameInto held j Δ keep
  rw [agreementRename] at a
  let l₂ := left.relabel j
  let r₂ := right.relabel j
  apply compositionValue allCounts ![append,.projection 0,.projection 1] (suc z)
    ![l₂,r₂] ![joined,l₂,r₂] (foldFromAgreement joined l₂ r₂ a)
  intro k
  exact Fin.cases ap (Fin.cases (projectionValue 0 ![l₂,r₂])
    (Fin.cases (projectionValue 1 ![l₂,r₂]) (fun i => Fin.elim0 i))) k

#print axioms exact_LiteralAgreementAccept
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountConverseProof
