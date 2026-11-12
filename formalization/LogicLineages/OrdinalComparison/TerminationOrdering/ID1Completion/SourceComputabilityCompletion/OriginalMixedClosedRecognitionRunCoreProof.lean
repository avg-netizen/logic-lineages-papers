module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionInductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceDescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionRunCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalRawListRepeat InternalRawListRepeatProof InternalRawListRepeatSupportProof
open OriginalMixedDirectBottomTrace
open OriginalMixedClosedRecognitionInductionDefinitions
open OriginalMixedClosedRecognitionInductionSyntaxProof
open OriginalMixedClosedRecognitionInductionBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Proof suppliers for the generic induction. Both are discharged by the
concrete closed-checker laws in OriginalMixedClosedRecognitionRunProof. -/
def FinishMap (body : Positive (Fin 1)) (source : Program 2) (leaf outLeaf : Program 4) : Prop :=
 ∀ (beta : Type) (Theta : List (Formula beta)) (out : OTerm beta),
 Nonempty (Derivation body Theta (graph1 (finish source leaf) (suc z) out)) →
 Nonempty (Derivation body Theta (graph1 (finish source outLeaf) (suc z) out))

def StepMap (body : Positive (Fin 1)) (source : Program 2) (leaf outLeaf : Program 4) : Prop :=
 ∀ (beta : Type) (Theta : List (Formula beta)) (state next : OTerm beta),
 Nonempty (Derivation body Theta (graph1 (transition source leaf) next state)) →
 Nonempty (Derivation body Theta (eqn next z).not) →
 Nonempty (Derivation body Theta (graph1 (transition source outLeaf) next state))

theorem atZero (source : Program 2) (leaf outLeaf : Program 4)
 (hfinish : FinishMap body source leaf outLeaf) (path out state : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn path z)))
 (hf : Nonempty (Derivation body Delta (fields source leaf path out state))) :
 Nonempty (Derivation body Delta (result source outLeaf path out state)) := by
 have hr := headTransport (repeatProgram (transition source leaf)) out path z
  (Fin.cons state Fin.elim0) he (andLeft hf)
 obtain ⟨hout⟩ := repeatZeroRecover (transition source leaf) out state hr
 have hz := outputTransport (repeatProgram (transition source outLeaf)) state out
  (Fin.cons z (Fin.cons state Fin.elim0)) ⟨symm hout⟩
  (repeatZeroValue (transition source outLeaf) state)
 obtain ⟨he⟩ := he
 have hrun := headTransport (repeatProgram (transition source outLeaf)) out z path
  (Fin.cons state Fin.elim0) ⟨symm he⟩ hz
 exact andIntro hrun (hfinish alpha Delta out (andRight hf))

/-- Query the actual old successor, transfer only this successful step, and
rebuild the same run using the internally quantified smaller-path row. -/
theorem atCons (source : Program 2) (leaf outLeaf : Program 4)
 (hstep : StepMap body source leaf outLeaf)
 (path head tail out state : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath source leaf outLeaf path)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hf : Nonempty (Derivation body Delta (fields source leaf path out state))) :
 Nonempty (Derivation body Delta (result source outLeaf path out state)) := by
 apply programCases (transition source leaf) (Fin.cons state Fin.elim0) _
 intro beta rho Theta next hrho ht
 simp only [consTermRename,emptyRename] at ht
 rw [resultRename]
 have hi' := renameInto hi rho Theta hrho
 have hc' := renameInto hc rho Theta hrho
 have hf' := renameInto hf rho Theta hrho
 rw [belowPathRename] at hi'
 rw [graph2Rename] at hc'
 rw [fieldsRename] at hf'
 have htail := frontConsForward (transition source leaf)
  (path.relabel rho) (head.relabel rho) (tail.relabel rho) (out.relabel rho)
  (state.relabel rho) next hc' ht (andLeft hf')
 have hnonzero := OriginalMixedDirectBottomTraceDescentProof.acceptingRunNonzero
  source leaf (out.relabel rho) (tail.relabel rho) next htail (andRight hf')
 have hnext := hstep beta Theta (state.relabel rho) next ht hnonzero
 have hless := InternalListCodecDecompositionSupportProof.consTailDescent
  (path.relabel rho) (head.relabel rho) (tail.relabel rho) hc'
 have hchild := belowPathApply source leaf outLeaf (path.relabel rho)
  (tail.relabel rho) (out.relabel rho) next hi' hless (andIntro htail (andRight hf'))
 have hrun := frontConsBackward (transition source outLeaf)
  (path.relabel rho) (head.relabel rho) (tail.relabel rho) (out.relabel rho)
  (state.relabel rho) next hc' hnext (andLeft hchild)
 exact andIntro hrun (andRight hchild)

theorem atCore (source : Program 2) (leaf outLeaf : Program 4)
 (hfinish : FinishMap body source leaf outLeaf) (hstep : StepMap body source leaf outLeaf)
 (path out state : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath source leaf outLeaf path)))
 (hf : Nonempty (Derivation body Delta (fields source leaf path out state))) :
 Nonempty (Derivation body Delta (result source outLeaf path out state)) := by
 apply OriginalContextInsertionLengthProof.listCases path _
 · exact atZero source leaf outLeaf hfinish path out state
    ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hf (eqn path z))
 · intro beta rho Theta head tail hrho hc
   rw [resultRename]
   have hi' := renameInto hi rho Theta hrho
   have hf' := renameInto hf rho Theta hrho
   rw [belowPathRename] at hi'
   rw [fieldsRename] at hf'
   exact atCons source leaf outLeaf hstep (path.relabel rho) head tail
    (out.relabel rho) (state.relabel rho) hi' hc hf'

/-- The original arithmetic strong-induction rule binds both states inside
every row, so it applies to arbitrary actual successors of an accepting run. -/
theorem rows (source : Program 2) (leaf outLeaf : Program 4)
 (hfinish : FinishMap body source leaf outLeaf) (hstep : StepMap body source leaf outLeaf)
 (path : OTerm alpha) : Nonempty (Derivation body Delta (AtPath source leaf outLeaf path)) := by
 apply pathInduction source leaf outLeaf path
 intro beta Theta code hi
 apply atPathIntro
 unfold matrix
 let A : Formula (beta ⊕ Fin 2) := fields source leaf (code.relabel Sum.inl)
  (.var (.inr 0)) (.var (.inr 1))
 let Xi := A :: Theta.map (fun q => q.relabel Sum.inl)
 have hf : Nonempty (Derivation body Xi A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hi' := renameInto hi (Sum.inl : beta → beta ⊕ Fin 2) Xi
  (by intro f h; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,h,rfl⟩))
 rw [belowPathRename] at hi'
 obtain ⟨r⟩ := atCore source leaf outLeaf hfinish hstep (code.relabel Sum.inl)
  (.var (.inr 0)) (.var (.inr 1)) hi' hf
 exact ⟨Derivation.implicationIntroduction r⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionRunCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionRunCoreProof
