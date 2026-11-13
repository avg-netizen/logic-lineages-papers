module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentArgumentNormalizationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalTagArithmeticSupportProof (refl)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem actualFields (H : Program 1) (M W : Program 2)
 (job role typed typ rawJob raw gamma c : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (ha : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W role typ raw gamma c)))
 (hr : Nonempty (Derivation body Delta (equal role (numeral 1))))
 (hzero : Nonempty (Derivation body Delta (equal typ (numeral 0)))) :
 Nonempty (Derivation body Delta
   (graph2 InternalPairing.pairing job (numeral 1) typed ⊓
    (graph2 InternalPairing.pairing typed (numeral 0) rawJob ⊓
     OriginalInternalJobAdmissible.Admissible H M W (numeral 1) (numeral 0) raw gamma c))) := by
 have hre := hr
 have hte := hzero
 rw [equalEqn] at hre hte
 have hj' := headTransport InternalPairing.pairing job role (numeral 1) (Fin.cons typed Fin.elim0) hre hj
 have ht' := headTransport InternalPairing.pairing typed typ (numeral 0) (Fin.cons rawJob Fin.elim0) hte ht
 let xs : Fin 5 → OTerm alpha := ![role,typ,raw,gamma,c]
 let ys : Fin 5 → OTerm alpha := ![numeral 1,numeral 0,raw,gamma,c]
 have he : ∀ i, Nonempty (Derivation body Delta (equal (xs i) (ys i))) := by
   intro i
   refine Fin.cases hr (Fin.cases hzero (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))))) i
   · rw [equalEqn]; exact ⟨refl raw⟩
   · rw [equalEqn]; exact ⟨refl gamma⟩
   · rw [equalEqn]; exact ⟨refl c⟩
 have ha' := OriginalInternalJobAdmissibleTransportProof.tupleTransport H M W xs ys he ha
 exact andIntro hj' (andIntro ht' ha')
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentArgumentNormalizationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentArgumentNormalizationProof
