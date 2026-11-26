module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixTrimProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTickIterationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixChildProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename headTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm trans addSucc)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalOriginalOrderProof (orderCases)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.InternalNumericIteration (repeatGraph)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename inputsRename)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparseRawRunShapeMotiveProof (pairRename)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralLambdaPrefixMachineProof
open NumberedWindowInternalLiteralLambdaPrefixLiveOpenProof (bit5)
open NumberedWindowInternalLiteralLambdaPrefixScopeProof (fiveInputsRename)
open NumberedWindowInternalLiteralLambdaPrefixOwnExecutionProof
open NumberedWindowInternalLiteralLambdaPrefixTrimProof (exact_OpenTrimLambdaPrefix)
open NumberedWindowInternalLiteralTickIterationProof (shiftEarly)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Strip the actual parent tick and the excess fuel. The child passes
the SAME lexical prefix guard at its own actual witness length. -/
theorem exact_OpenLambdaPrefixChild (W : Program 3) (c t q w r c₁ t₁ q₁ w₁ r₁ : OTerm α)
    (first : D B Γ (programGraph (prefixTick W) (prefixStartTerm c₁ t₁ q₁ w₁ r₁) ![prefixStartTerm c t q w r]))
    (smaller : D B Γ (ltF w₁ w))
    (parent : D B Γ (bit5 (prefixOwn W) ![c,t,q,w,r])) :
    D B Γ (bit5 (prefixOwn W) ![c₁,t₁,q₁,w₁,r₁]) := by
  apply exact_OpenPrefixOwnExecution W c t q w r _ parent
  intro β j Δ out keep run unit
  simp only [bit5,programRename,fiveInputsRename,sucRelabel,zRelabel]
  have dec := renameInto smaller j Δ keep
  rw [orderRename] at dec
  apply orderCases Δ (w₁.relabel j) (w.relabel j) _ dec
  intro γ k Ω gap stay extra
  simp only [programRename,fiveInputsRename,sucRelabel,zRelabel]
  let old := prefixStartTerm ((c.relabel j).relabel k) ((t.relabel j).relabel k) ((q.relabel j).relabel k)
    ((w.relabel j).relabel k) ((r.relabel j).relabel k)
  let a := (c₁.relabel j).relabel k
  let b := (t₁.relabel j).relabel k
  let x := (q₁.relabel j).relabel k
  let v := (w₁.relabel j).relabel k
  let y := (r₁.relabel j).relabel k
  let next := prefixStartTerm a b x v y
  let final := out.relabel k
  have moved₀ := renameInto first j Δ keep
  simp only [programRename,inputsRename,prefixStartTermRename] at moved₀
  have moved := renameInto moved₀ k Ω stay
  simp only [programRename,inputsRename,prefixStartTermRename] at moved
  have prev := renameInto run k Ω stay
  simp only [programRename,pairRename,prefixStartTermRename] at prev
  obtain ⟨addend⟩ := extra
  have bound := trans (symm addend) (addSucc v gap)
  have last := headTransport (prefixLoop W) final ((w.relabel j).relabel k) (suc (add v gap)) ![old] ⟨bound⟩ prev
  have tail : D B Ω (repeatGraph (prefixTick W) final (add v gap) next) :=
    shiftEarly (prefixTick W) old next (add v gap) final moved last
  have flag := renameInto unit k Ω stay
  simp only [unaryRename,sucRelabel,zRelabel] at flag
  exact exact_OpenTrimLambdaPrefix W a b x v y gap final tail flag

#print axioms exact_OpenLambdaPrefixChild
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixChildProof
