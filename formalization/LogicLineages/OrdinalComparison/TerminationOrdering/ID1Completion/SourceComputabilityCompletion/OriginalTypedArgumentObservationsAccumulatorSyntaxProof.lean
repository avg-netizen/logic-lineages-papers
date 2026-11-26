module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationScanSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open OriginalTypedArgumentObservations OriginalTypedDecoderInternalLogicSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def accumulatorBody (R : Program 2) (count : OTerm alpha) : Formula (alpha ⊕ Fin 13) :=
 (graph2 InternalPairing.pairing (.var (.inr 4)) (.var (.inr 0)) (.var (.inr 1))).imp ((graph2 InternalPairing.pairing (.var (.inr 5)) (.var (.inr 0)) (.var (.inr 2))).imp ((graph2 InternalApplicationValidityStackAppend.append (.var (.inr 2)) (.var (.inr 1)) (.var (.inr 3))).imp ((graph3 (walk R) (.var (.inr 7)) (count.relabel Sum.inl) (.var (.inr 4)) (.var (.inr 6))).imp ((graph3 (walk R) (.var (.inr 8)) (count.relabel Sum.inl) (.var (.inr 5)) (.var (.inr 6))).imp ((graph2 InternalPairing.pairing (.var (.inr 7)) (.var (.inr 9)) (.var (.inr 11))).imp ((graph2 InternalPairing.pairing (.var (.inr 8)) (.var (.inr 10)) (.var (.inr 12))).imp (equal (.var (.inr 9)) (.var (.inr 10)) ⊓ graph2 InternalApplicationValidityStackAppend.append (.var (.inr 12)) (.var (.inr 11)) (.var (.inr 3)))))))))
def accumulatorRow (R : Program 2) (count : OTerm alpha) : Formula alpha := allBlock (accumulatorBody R count)

theorem accumulatorSubst {beta : Type} (R : Program 2) (count : OTerm alpha) (ts : alpha → OTerm beta) :
 (accumulatorRow R count).subst (fun a => emb (ts a)) = accumulatorRow R (count.subst ts) := by
 unfold accumulatorRow accumulatorBody graph2 graph3
 rw [allBlockSubst,liftedEmbedding]
 simp only [impSubst,conjunctionSubst,equalSubst,programSubst,consTermSubst,liftSubst,Term.subst,Sum.elim_inr,emptySubst]

theorem accumulatorRename {beta : Type} (R : Program 2) (count : OTerm alpha) (j : alpha → beta) :
 (accumulatorRow R count).relabel j = accumulatorRow R (count.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (accumulatorRow R count).subst (fun a => emb (.var (j a))) = _
 rw [accumulatorSubst]
 simp only [← termRelabelAsSubst]

theorem accumulatorWitness (R : Program 2) (count raw acc1 acc2 suffix initial1 initial2 parameter out1 out2 remaining1 remaining2 result1 result2 : OTerm alpha) :
 (accumulatorBody R count).subst (Sum.elim Term.var (fun i => emb (![raw,acc1,acc2,suffix,initial1,initial2,parameter,out1,out2,remaining1,remaining2,result1,result2] i))) =
 (graph2 InternalPairing.pairing initial1 raw acc1).imp ((graph2 InternalPairing.pairing initial2 raw acc2).imp ((graph2 InternalApplicationValidityStackAppend.append acc2 acc1 suffix).imp ((graph3 (walk R) out1 count initial1 parameter).imp ((graph3 (walk R) out2 count initial2 parameter).imp ((graph2 InternalPairing.pairing out1 remaining1 result1).imp ((graph2 InternalPairing.pairing out2 remaining2 result2).imp (equal remaining1 remaining2 ⊓ graph2 InternalApplicationValidityStackAppend.append result2 result1 suffix))))))) := by
 have he : (Sum.elim Term.var (fun i => emb (![raw,acc1,acc2,suffix,initial1,initial2,parameter,out1,out2,remaining1,remaining2,result1,result2] i))) =
   (fun a => emb (Sum.elim Term.var ![raw,acc1,acc2,suffix,initial1,initial2,parameter,out1,out2,remaining1,remaining2,result1,result2] a)) := by
   funext a
   cases a <;> rfl
 unfold accumulatorBody graph2 graph3
 rw [he]
 simp only [impSubst,conjunctionSubst,equalSubst,programSubst,consTermSubst,witnessLift,Term.subst,Sum.elim_inr,emptySubst]
 rfl

theorem accumulatorInstantiate (R : Program 2) (count : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
 instantiate (accumulatorRow R count) (emb t) = accumulatorRow R (count.subst (bindTerm t)) := by
 rw [instantiate,bindEmbedding,accumulatorSubst]
theorem accumulatorSuccessor (R : Program 2) (count : OTerm (alpha ⊕ Fin 1)) :
 successorInstance (accumulatorRow R count) = accumulatorRow R (count.subst nextTerm) := by
 rw [successorInstance,nextEmbedding,accumulatorSubst]

theorem accumulatorApply (R : Program 2) (count raw acc1 acc2 suffix initial1 initial2 parameter out1 out2 remaining1 remaining2 result1 result2 : OTerm alpha)
 (hrow : Nonempty (Derivation body Delta (accumulatorRow R count)))
 (h0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial1 raw acc1)))
 (h1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial2 raw acc2)))
 (h2 : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append acc2 acc1 suffix)))
 (h3 : Nonempty (Derivation body Delta (graph3 (walk R) out1 count initial1 parameter)))
 (h4 : Nonempty (Derivation body Delta (graph3 (walk R) out2 count initial2 parameter)))
 (h5 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out1 remaining1 result1)))
 (h6 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out2 remaining2 result2)))
 : Nonempty (Derivation body Delta (equal remaining1 remaining2 ⊓ graph2 InternalApplicationValidityStackAppend.append result2 result1 suffix)) := by
 have h := actualFiniteUniversalElimination body alpha 13 Delta (accumulatorBody R count)
   (fun i => emb (![raw,acc1,acc2,suffix,initial1,initial2,parameter,out1,out2,remaining1,remaining2,result1,result2] i)) hrow
 rw [accumulatorWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨h0⟩ := h0
 obtain ⟨h1⟩ := h1
 obtain ⟨h2⟩ := h2
 obtain ⟨h3⟩ := h3
 obtain ⟨h4⟩ := h4
 obtain ⟨h5⟩ := h5
 obtain ⟨h6⟩ := h6
 exact ⟨(Derivation.implicationElimination (Derivation.implicationElimination (Derivation.implicationElimination (Derivation.implicationElimination (Derivation.implicationElimination (Derivation.implicationElimination (Derivation.implicationElimination h h0) h1) h2) h3) h4) h5) h6)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorSyntaxProof
