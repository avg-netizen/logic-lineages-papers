module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressCarrierProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressLowerProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreInstalledCertificateProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionProgressSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplicationSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.SourceComputabilityCompletion.InverseApplicationSyntaxProof (membershipRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectCoreInstalledCertificateProof (exact_InstalledCertificateSharedTape)
open NumberedWindowInternalDirectBoundaryOpenProof (exact_OpenRawGuards)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (keepThrough)
open NumberedWindowInternalCertifiedUnionProgressSupportProof (oddIntroduction oddCertificateCases)
open NumberedWindowInternalScalarSingletonInductionProof
  (singletonCode singletonJ scalarLower exact_ActualScalarSingletonProgressiveInduction)
open NumberedWindowInternalLiteralSingletonProgressSyntaxProof
  (scalarLowerRename oddCertificateRename singletonCodeRename)
open NumberedWindowInternalLiteralSingletonProgressCarrierProof (exact_LiteralSingletonCarrierFromScalar)
open NumberedWindowInternalLiteralSingletonProgressLowerProof (exact_LiteralSingletonLowerMembers)
open NumberedWindowInternalLiteralSingletonProgressTargets

private theorem targetMembership (i : Program 1) (r : Program 3) (c : Nat)
    (fold : SingletonTargetFoldSupply i r c) (α : Type) (Γ : List (Formula α)) (head dst w : OTerm α)
    (lower : Nonempty (Derivation (sourceBody (literalData i r) c) Γ (scalarLower (literalData i r) c head)))
    (cert : Nonempty (Derivation (sourceBody (literalData i r) c) Γ
      (certificate (literalData i r) true c (singletonCode head) dst w))) :
    Nonempty (Derivation (sourceBody (literalData i r) c) Γ (membership true dst)) := by
  let S := literalData i r
  let B := sourceBody S c
  apply exact_InstalledCertificateSharedTape i (jRaw i) r permutation c α Γ
    (singletonCode head) w dst (membership true dst) cert
  intro β ρ Δ _ removed _ _ _ _ _ _ _ _ _ keep _ _ boundary _
  rw [membershipRename]
  apply exact_OpenRawGuards i B β Δ ((singletonCode head).relabel ρ) (dst.relabel ρ)
    removed (membership true (dst.relabel ρ)) boundary
  intro γ τ Ω _ decoded _ _ _ retain facts
  rw [membershipRename]
  let g := τ ∘ ρ
  let Q := (head.relabel ρ).relabel τ
  let V := (dst.relabel ρ).relabel τ
  let W := (w.relabel ρ).relabel τ
  have preserved := keepThrough ρ τ keep retain
  have lowerNow : Nonempty (Derivation B Ω (scalarLower S c Q)) := by
    simpa only [Q,g,scalarLowerRename,Term.relabel_relabel] using renameInto lower g Ω preserved
  have accepted : Nonempty (Derivation B Ω (certificate S true c (singletonCode Q) V W)) := by
    simpa only [Q,V,W,g,oddCertificateRename,singletonCodeRename,Term.relabel_relabel] using
      renameInto cert g Ω preserved
  have descendants := exact_LiteralSingletonLowerMembers i r c γ Ω Q V W decoded
    lowerNow accepted facts.parsed.kept
  exact fold γ Ω V decoded facts.parsed.kept facts.targetTyped descendants

private theorem localProgress (i : Program 1) (r : Program 3) (c : Nat)
    (fold : SingletonTargetFoldSupply i r c) (α : Type) (Γ : List (Formula α)) (head : OTerm α)
    (typed : Nonempty (Derivation (sourceBody (literalData i r) c) Γ (carrier (literalData i r) false c head)))
    (lower : Nonempty (Derivation (sourceBody (literalData i r) c) Γ (scalarLower (literalData i r) c head))) :
    Nonempty (Derivation (sourceBody (literalData i r) c) Γ (singletonJ head)) := by
  let S := literalData i r
  let B := sourceBody S c
  change Nonempty (Derivation B Γ (membership true (singletonCode head)))
  apply oddIntroduction S c Γ (singletonCode head) (exact_LiteralSingletonCarrierFromScalar i r c α Γ head typed)
  intro β ρ Δ dst keep strict
  have actual : Nonempty (Derivation B Δ (edge S true c (singletonCode (head.relabel ρ)) dst)) := by
    simpa only [singletonCodeRename] using strict
  apply oddCertificateCases S c Δ (singletonCode (head.relabel ρ)) dst (membership true dst) actual
  intro γ τ Ω w retain cert
  let g := τ ∘ ρ
  let Q := (head.relabel ρ).relabel τ
  let V := dst.relabel τ
  have saved : Nonempty (Derivation B Ω (scalarLower S c Q)) := by
    simpa only [Q,g,scalarLowerRename,Term.relabel_relabel] using
      renameInto lower g Ω (keepThrough ρ τ keep retain)
  have same : Nonempty (Derivation B Ω (certificate S true c (singletonCode Q) V w)) := by
    simpa only [Q,V,singletonCodeRename] using cert
  rw [membershipRename]
  exact targetMembership i r c fold γ Ω Q V w saved same

theorem exact_LiteralSingletonPromotionFromFold : ExactLiteralSingletonPromotionFromFold := by
  intro i r c fold α Γ q
  let S := literalData i r
  let B := sourceBody S c
  apply exact_ActualScalarSingletonProgressiveInduction S c α Γ q
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let C := carrier S false c x
  let L := scalarLower S c x
  let Δ := C :: L :: Γ.map weaken
  have typed : Nonempty (Derivation B Δ C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have lower : Nonempty (Derivation B Δ L) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  exact localProgress i r c fold (α ⊕ Fin 1) Δ x typed lower

#print axioms exact_LiteralSingletonPromotionFromFold
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressProof
