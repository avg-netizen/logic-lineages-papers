module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleShapeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportRejectedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleModeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalInternalJobAdmissible
open OriginalUniverseDecoderInternalAcceptance
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBetaTotalityProof (disjunctionElimination)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem argumentsImpossible (H : Program 1) (M W : Program 2)
 (raw gamma c tag payload : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (ArgumentsWitness H M W raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
 (h6 : Nonempty (Derivation body Delta (equal tag (numeral 6)).not))
 (h7 : Nonempty (Derivation body Delta (equal tag (numeral 7)).not)) :
 Nonempty (Derivation body Delta (⊥ : Formula alpha)) := by
 obtain ⟨ht⟩ := OriginalInternalJobAdmissibleShapeProof.witnessTags H M W raw gamma c tag payload ha hp
 have l : Nonempty (Derivation body (equal tag (numeral 6) :: Delta) (⊥ : Formula alpha)) :=
  ⟨Derivation.implicationElimination (Classical.choice (withHyp h6 _)) (Derivation.hypothesis List.mem_cons_self)⟩
 have r : Nonempty (Derivation body (equal tag (numeral 7) :: Delta) (⊥ : Formula alpha)) :=
  ⟨Derivation.implicationElimination (Classical.choice (withHyp h7 _)) (Derivation.hypothesis List.mem_cons_self)⟩
 exact ⟨disjunctionElimination ht (Derivation.implicationIntroduction (Classical.choice l))
  (Derivation.implicationIntroduction (Classical.choice r))⟩
theorem termMode (H : Program 1) (M W : Program 2)
 (role typ raw gamma c tag payload : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
 (h6 : Nonempty (Derivation body Delta (equal tag (numeral 6)).not))
 (h7 : Nonempty (Derivation body Delta (equal tag (numeral 7)).not)) :
 Nonempty (Derivation body Delta (equal role (numeral 0) ⊓ TermAccepted H M W typ raw gamma c)) := by
 let A := equal role (numeral 0) ⊓ TermAccepted H M W typ raw gamma c
 let B := equal role (numeral 1) ⊓ (equal typ (numeral 0) ⊓ ArgumentsWitness H M W raw gamma c)
 have hl : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hr : Nonempty (Derivation body (B :: Delta) A) := by
  have h : Nonempty (Derivation body (B :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := argumentsImpossible H M W raw gamma c tag payload (andRight (andRight h))
   (withHyp hp B) (withHyp h6 B) (withHyp h7 B)
  exact ⟨Derivation.explosion hf⟩
 exact ⟨disjunctionElimination (Classical.choice ha)
  (Derivation.implicationIntroduction (Classical.choice hl)) (Derivation.implicationIntroduction (Classical.choice hr))⟩
theorem consMode (H : Program 1) (M W : Program 2)
 (role typ raw gamma c payload : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 7) payload))) :
 Nonempty (Derivation body Delta
  (equal role (numeral 1) ⊓ (equal typ (numeral 0) ⊓ ArgumentsWitness H M W raw gamma c))) := by
 let A := equal role (numeral 0) ⊓ TermAccepted H M W typ raw gamma c
 let B := equal role (numeral 1) ⊓ (equal typ (numeral 0) ⊓ ArgumentsWitness H M W raw gamma c)
 have hl : Nonempty (Derivation body (A :: Delta) B) := by
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact OriginalUniverseDecoderTransportRejectedProof.termSeven H M W raw payload typ gamma c B
   (withHyp hp A) (andRight h)
 have hr : Nonempty (Derivation body (B :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 exact ⟨disjunctionElimination (Classical.choice ha)
  (Derivation.implicationIntroduction (Classical.choice hl)) (Derivation.implicationIntroduction (Classical.choice hr))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleModeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleModeProof
