module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnTermQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnListQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSourceCases
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnShapeCompletion
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSupportProof (refl)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open UniformReturnSupplierProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem weakenInto {phi : Formula alpha} (h : Nonempty (Derivation body Delta phi))
 (Theta : List (Formula alpha)) (hi : ∀ f ∈ Delta, f ∈ Theta) :
 Nonempty (Derivation body Theta phi) := by
 obtain ⟨h⟩ := h
 exact ⟨Derivation.weakening hi h⟩
theorem supplierWeaken (Theta : List (Formula alpha))
 (children deletions produced first second row : OTerm alpha)
 (hi : ∀ f ∈ Delta, f ∈ Theta)
 (hs : Supplier body Delta children deletions produced first second row) :
 Supplier body Theta children deletions produced first second row := by
 intro beta j Xi old results hj ha
 exact hs beta j Xi old results (fun f hf => hj f (hi f hf)) ha
theorem fromShape (R : Program 2)
 (job role typed typ rawJob raw parameter children deletions counts payload frame produced first second row tag rawPayload : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hraw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag rawPayload)))
 (hshape : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.ReturnShape role typ tag)))
 (hs : Supplier body Delta children deletions produced first second row) :
 Nonempty (Derivation body Delta (UniformReturnDefinitions.Completion R frame produced)) := by
 apply UniformReturnSourceCases.shapeCases role typ raw tag rawPayload _ hraw hshape
 · intro Theta hi he
   have hj' := weakenInto hj Theta hi
   have ht' := weakenInto ht Theta hi
   have hr' := weakenInto hr Theta hi
   have hc' := weakenInto hc Theta hi
   have hp' := weakenInto hp Theta hi
   have hf' := weakenInto hf Theta hi
   have hjob := PrefixFrameIdentityProof.binaryInputs InternalPairing.pairing job role typed (numeral 0) typed he ⟨refl typed⟩ hj'
   have hs' := supplierWeaken Theta children deletions produced first second row hi hs
   exact UniformReturnTermQueries.termCompletion R job typed typ rawJob raw parameter children deletions counts payload frame produced first second row
     hjob ht' hr' hc' hp' hf' hs'
 · intro Theta hi he htag
   have hj' := weakenInto hj Theta hi
   have ht' := weakenInto ht Theta hi
   have hr' := weakenInto hr Theta hi
   have hc' := weakenInto hc Theta hi
   have hp' := weakenInto hp Theta hi
   have hf' := weakenInto hf Theta hi
   have hjob := PrefixFrameIdentityProof.binaryInputs InternalPairing.pairing job role typed (numeral 1) typed he ⟨refl typed⟩ hj'
   have hs' := supplierWeaken Theta children deletions produced first second row hi hs
   exact UniformReturnListQueries.nilCompletion R job typed typ rawJob raw parameter children deletions counts payload frame produced first second row rawPayload
     hjob ht' hr' hc' hp' hf' htag hs'
 · intro Theta hi he htag
   have hj' := weakenInto hj Theta hi
   have ht' := weakenInto ht Theta hi
   have hr' := weakenInto hr Theta hi
   have hc' := weakenInto hc Theta hi
   have hp' := weakenInto hp Theta hi
   have hf' := weakenInto hf Theta hi
   have hjob := PrefixFrameIdentityProof.binaryInputs InternalPairing.pairing job role typed (numeral 1) typed he ⟨refl typed⟩ hj'
   have hs' := supplierWeaken Theta children deletions produced first second row hi hs
   exact UniformReturnListQueries.consCompletion R job typed typ rawJob raw parameter children deletions counts payload frame produced first second row rawPayload
     hjob ht' hr' hc' hp' hf' htag hs'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnShapeCompletion
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnShapeCompletion
