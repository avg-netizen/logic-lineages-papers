module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceCertificateProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open GuardedSource GuardedSourceGraphSupportProof InternalGraphCompositionSyntaxProof
open InternalFiniteBlocksBindingProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel zSubst sucSubst)
open SourceComputabilityFormulaSupportProof

@[simp] theorem numeralRename {α β : Type} (n : Nat) (j : α → β) :
    (numeral n : OTerm α).relabel j = numeral n := by
  induction n with
  | zero => exact zRelabel j
  | succ n ih => simpa only [numeral,sucRelabel] using congrArg suc ih

theorem literalTypedGraph {α : Type} (data : JointGammaComputability.Data) (context : Nat)
    (typ x : OTerm α) :
    literalTyped data context typ x = programGraph data.typed (suc z) ![numeral context,typ,x] := by
  unfold literalTyped JointGammaTyped.typedFormula
  rw [applyGraphSubst]
  unfold programGraph graph
  congr 1
  congr 1
  · simp only [sucSubst,zSubst]
  · funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q))) i

/-- This is a syntax equality for the ORIGINAL existential certificate,
not an alternate relation or a selected semantic certificate. -/
theorem literalRGraph {α : Type} (data : SourcePresentation.Data) (context : Nat)
    (x y : OTerm α) :
    literalR data context x y = existsOne
      (programGraph data.positive (suc z)
        ![numeral context,x.relabel Sum.inl,y.relabel Sum.inl,.var (.inr (0 : Fin 1))]) := by
  unfold literalR OrdinaryArithmeticQuotient.certificateGraph
  rw [existsFinSubst,actualOriginalBlockEmbedding]
  change existsOne (arithmeticEmbedding.onFormula _) = _
  congr 1
  rw [applyGraphSubst]
  unfold programGraph graph
  congr 1
  congr 1
  · simp only [sucSubst,zSubst]
  · funext i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q)))) i
    · exact numeralRename context Sum.inl
    · rfl
    · rfl
    · rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
