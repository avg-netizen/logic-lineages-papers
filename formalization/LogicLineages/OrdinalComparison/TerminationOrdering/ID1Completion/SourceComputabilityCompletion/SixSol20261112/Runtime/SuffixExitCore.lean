module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SuffixExitSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ProtectedPrefixProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SuffixExitCore
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalFiniteBlocksSubstitutionProof (renameIdentity)
open OriginalHereditaryPotentialCompletionSyntaxProof (emptyRename)
open SuffixExitWorkingTargets SuffixExitSyntax
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem weakenConsumer (R : Program 2) (suffix output : OTerm alpha) (psi : Formula alpha)
 {Theta : List (Formula alpha)} (next : Consumer R body Delta suffix output psi)
 (inc : ∀ f ∈ Delta, f ∈ Theta) : Consumer R body Theta suffix output psi := by
 intro beta j Xi count input results hinc hp hr he
 exact next beta j Xi count input results (fun f hf => hinc f (inc f hf)) hp hr he
theorem renameConsumer (R : Program 2) (suffix output : OTerm alpha) (psi : Formula alpha)
 {beta : Type} (j : alpha → beta) (Theta : List (Formula beta))
 (next : Consumer R body Delta suffix output psi) (inc : ∀ f ∈ Delta, f.relabel j ∈ Theta) :
 Consumer R body Theta (suffix.relabel j) (output.relabel j) (psi.relabel j) := by
 intro gamma k Xi count input results hinc hp hr he
 have h := next gamma (k ∘ j) Xi count input results
   (by
     intro f hf
     simpa only [← InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hinc _ (inc f hf))
   (by simpa only [Term.relabel_relabel] using hp)
   (by simpa only [Term.relabel_relabel] using hr)
   (by simpa only [Term.relabel_relabel] using he)
 simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using h
theorem consumerApply (R : Program 2) (suffix output count input results : OTerm alpha) (psi : Formula alpha)
 (next : Consumer R body Delta suffix output psi)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input suffix results)))
 (hr : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output count input)))
 (he : Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty output))) :
 Nonempty (Derivation body Delta psi) := by
 have h := next alpha id Delta count input results
   (by intro f hf; simpa only [renameIdentity] using hf)
   (by simpa only [Term.relabel_id] using hp)
   (by simpa only [Term.relabel_id] using hr)
   (by simpa only [Term.relabel_id] using he)
 simpa only [renameIdentity] using h
theorem emptyContradiction (input work results head tail : OTerm alpha) (psi : Formula alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work head tail)))
 (he : Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty input))) :
 Nonempty (Derivation body Delta psi) := by
 obtain ⟨hz⟩ := valueUnique InternalUnpair.left work z (Fin.cons input Fin.elim0) (InternalApplicationCertificateConstructorsSupportProof.pairLeft input work results hs) he
 obtain ⟨hn⟩ := OriginalTypedDecoderInternalListProof.consNonzero work head tail hw
 exact ⟨Derivation.explosion (Derivation.implicationElimination hn (by simpa only [equalEqn,SourceComputabilityFormulaSupportProof.numeral] using hz))⟩
theorem zeroPrefix (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B suffix output count input work results front : OTerm alpha) (psi : Formula alpha)
 (hf : Nonempty (Derivation body Delta (fields R H M W c B suffix output count input work results front)))
 (hz : Nonempty (Derivation body Delta (eqn front z)))
 (next : Consumer R body Delta suffix output psi) : Nonempty (Derivation body Delta psi) := by
 have ha := headTransport InternalApplicationValidityStackAppend.append work front z (Fin.cons suffix Fin.elim0)
   hz (andLeft (andRight (andRight hf)))
 have he := InternalApplicationValidityStackAppendListProof.appendZeroRecover work suffix ha
 have hp := headTransport InternalPairing.pairing input work suffix (Fin.cons results Fin.elim0) he (andLeft hf)
 exact consumerApply R suffix output count input results psi next hp
   (andLeft (andRight (andRight (andRight hf)))) (andRight (andRight (andRight (andRight hf))))
theorem zeroCore (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B suffix output input work results front : OTerm alpha) (psi : Formula alpha)
 (hf : Nonempty (Derivation body Delta (fields R H M W c B suffix output z input work results front)))
 (next : Consumer R body Delta suffix output psi) : Nonempty (Derivation body Delta psi) := by
 apply OriginalContextInsertionLengthProof.listCases front psi
 · let A := eqn front z
   have inc : ∀ f ∈ Delta, f ∈ A :: Delta := fun f hf => List.mem_cons_of_mem _ hf
   exact zeroPrefix R H M W c B suffix output z input work results front psi
     (weakenProof hf inc) ⟨Derivation.hypothesis List.mem_cons_self⟩ (weakenConsumer R suffix output psi next inc)
 · intro beta j Theta head tail hinc hc
   apply programCases InternalApplicationValidityStackAppend.append (Fin.cons tail (Fin.cons (suffix.relabel j) Fin.elim0)) _
   intro gamma k Xi rest hk hrest
   simp only [consTermRename,InternalControlGraphSupportProof.emptyRename] at hrest
   have hf' := renameInto (renameInto hf j Theta hinc) k Xi hk
   simp only [fieldsRename,zRelabel] at hf'
   have hc' := renameInto hc k Xi hk
   rw [graph2Rename] at hc'
   have hw := InternalApplicationValidityStackAppendListProof.consForward
     ((front.relabel j).relabel k) (head.relabel k) (tail.relabel k) ((suffix.relabel j).relabel k)
     rest ((work.relabel j).relabel k) hc' hrest (andLeft (andRight (andRight hf')))
   have heq := InternalNumericIterationSupportProof.repeatZeroRecover (OriginalHereditaryCombinedStep.step R)
     ((output.relabel j).relabel k) ((input.relabel j).relabel k) (andLeft (andRight (andRight (andRight hf'))))
   have he := headTransport InternalUnpair.left z ((output.relabel j).relabel k) ((input.relabel j).relabel k)
     Fin.elim0 heq (andRight (andRight (andRight (andRight hf'))))
   exact emptyContradiction ((input.relabel j).relabel k) ((work.relabel j).relabel k) ((results.relabel j).relabel k)
     (head.relabel k) rest ((psi.relabel j).relabel k) (andLeft hf') hw he
theorem succCore (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B suffix output count input work results front : OTerm alpha) (psi : Formula alpha)
 (hi : Nonempty (Derivation body Delta (row R H M W c B suffix output count psi)))
 (hf : Nonempty (Derivation body Delta (fields R H M W c B suffix output (suc count) input work results front)))
 (next : Consumer R body Delta suffix output psi) : Nonempty (Derivation body Delta psi) := by
 apply OriginalContextInsertionLengthProof.listCases front psi
 · let A := eqn front z
   have inc : ∀ f ∈ Delta, f ∈ A :: Delta := fun f hf => List.mem_cons_of_mem _ hf
   exact zeroPrefix R H M W c B suffix output (suc count) input work results front psi
     (weakenProof hf inc) ⟨Derivation.hypothesis List.mem_cons_self⟩ (weakenConsumer R suffix output psi next inc)
 · intro beta j Theta head tail hinc hc
   have hf' := renameInto hf j Theta hinc
   simp only [fieldsRename,sucRelabel] at hf'
   apply ProtectedPrefixProof.actualStepCases R H M W body beta Theta
     (c.relabel j) (B.relabel j) (input.relabel j) (work.relabel j) (results.relabel j)
     (front.relabel j) head tail (suffix.relabel j) (psi.relabel j)
     (andLeft hf') (andLeft (andRight (andRight hf'))) hc (andLeft (andRight hf'))
   intro gamma k Xi newPrefix nextWork nextResults step hk hp ht ha hs
   have hi' := renameInto (renameInto hi j Theta hinc) k Xi hk
   simp only [rowRename] at hi'
   have hf'' := renameInto hf' k Xi hk
   simp only [fieldsRename,sucRelabel] at hf''
   have hr := InternalNumericIterationProof.frontSuccForward (OriginalHereditaryCombinedStep.step R)
     ((count.relabel j).relabel k) ((output.relabel j).relabel k) ((input.relabel j).relabel k) step
     ht (andLeft (andRight (andRight (andRight hf''))))
   exact rowApply R H M W ((c.relabel j).relabel k) ((B.relabel j).relabel k) ((suffix.relabel j).relabel k)
     ((output.relabel j).relabel k) ((count.relabel j).relabel k) step nextWork nextResults newPrefix ((psi.relabel j).relabel k)
     hi' (andIntro hp (andIntro ha (andIntro hs (andIntro hr (andRight (andRight (andRight (andRight hf''))))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SuffixExitCore
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SuffixExitCore
