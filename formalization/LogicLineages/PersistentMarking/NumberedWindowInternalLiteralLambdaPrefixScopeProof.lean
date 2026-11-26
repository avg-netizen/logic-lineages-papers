module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixScopeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename inputsRename)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (stateRename)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralLambdaFrameOpenPartsProof (LambdaParts lambdaWitnessRename rawLambdaRename)
open NumberedWindowInternalLiteralLambdaPrefixMachineProof
open NumberedWindowInternalLiteralLambdaPrefixLiveOpenProof (bit5)
open NumberedWindowInternalLiteralLambdaPrefixReportsProof (exact_OpenPrefixLexicalReportsAt)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem fiveInputsRename {β : Type} (c t q w r : OTerm α) (j : α → β) :
    (fun i : Fin 5 => ((![c,t,q,w,r] : Fin 5 → OTerm α) i).relabel j) =
      ![c.relabel j,t.relabel j,q.relabel j,w.relabel j,r.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun e => Fin.elim0 e))))) i

theorem movePrefixBit {β : Type} (p : Program 5) (c t q w r : OTerm α)
    (j : α → β) (Δ : List (Formula β)) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    (checked : D B Γ (bit5 p ![c,t,q,w,r])) :
    D B Δ (bit5 p ![c.relabel j,t.relabel j,q.relabel j,w.relabel j,r.relabel j]) := by
  have h := renameInto checked j Δ keep
  simpa only [bit5,programRename,fiveInputsRename,sucRelabel,zRelabel] using h

theorem exact_OpenPrefixLexicalCases (W : Program 3)
    (c t q w r d a inner e b : OTerm α) (goal : Formula α)
    (head : D B Γ (unary cellHead (numeral 2) q))
    (row : LambdaParts B Γ q w r d a inner e b)
    (gate : D B Γ (bit5 (prefixOwn W) ![c,t,q,w,r]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (cod : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (eqn (t.relabel j) (rawCons (d.relabel j) cod)) →
      D B Δ (windowAt W (rawCons (d.relabel j) (c.relabel j)) cod (a.relabel j)) →
      D B Δ (windowAt W (rawCons (d.relabel j) (c.relabel j)) cod (b.relabel j)) →
      D B Δ (programGraph (prefixTick W)
        (prefixStartTerm (rawCons (d.relabel j) (c.relabel j)) cod (a.relabel j) (inner.relabel j) (b.relabel j))
        ![prefixStartTerm (c.relabel j) (t.relabel j) (q.relabel j) (w.relabel j) (r.relabel j)]) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  apply programCases cellHead ![t] goal
  intro β j Δ dom keep domReport
  apply programCases cellTail ![t.relabel j] (goal.relabel j)
  intro γ k Ω cod stay tailReport
  let m := k ∘ j
  have all (f : Formula α) (hf : f ∈ Γ) : f.relabel m ∈ Ω := by
    simpa only [m,formulaRelabelComposition,Function.comp_assoc] using stay _ (keep f hf)
  have held := movePrefixBit (prefixOwn W) c t q w r m Ω all gate
  have first := renameInto head m Ω all
  rw [unaryRename,numeralRename] at first
  have src := renameInto row.source m Ω all
  have wrd := renameInto row.witness m Ω all
  have dst := renameInto row.target m Ω all
  have binder := renameInto row.binder m Ω all
  simp only [eqnRelabel,rawLambdaRename] at src dst
  simp only [eqnRelabel,lambdaWitnessRename] at wrd
  simp only [eqnRelabel] at binder
  have lSlot := renameInto row.sourceSlot m Ω all
  have wSlot := renameInto row.childSlot m Ω all
  have rSlot := renameInto row.targetSlot m Ω all
  simp only [programRename,NumberedWindowInternalSparseFieldParserOpenSyntaxProof.tripleInputsRename] at lSlot wSlot rSlot
  have data : LambdaParts B Ω (q.relabel m) (w.relabel m) (r.relabel m)
      (d.relabel m) (a.relabel m) (inner.relabel m) (e.relabel m) (b.relabel m) :=
    ⟨src,wrd,dst,binder,lSlot,wSlot,rSlot⟩
  rw [inputsRename] at domReport
  have fst := renameInto domReport k Ω stay
  rw [programRename,inputsRename,Term.relabel_relabel] at fst
  rw [inputsRename,Term.relabel_relabel] at tailReport
  obtain ⟨arrow,l,r,step⟩ := exact_OpenPrefixLexicalReportsAt W (c.relabel m) (t.relabel m) (q.relabel m)
    (w.relabel m) (r.relabel m) (d.relabel m) (a.relabel m) (inner.relabel m) (e.relabel m) (b.relabel m)
    (dom.relabel k) cod first data held fst tailReport
  have result := use γ m Ω cod all arrow l r step
  simpa only [m,formulaRelabelComposition,Function.comp_assoc] using result

#print axioms fiveInputsRename
#print axioms movePrefixBit
#print axioms exact_OpenPrefixLexicalCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixScopeProof
