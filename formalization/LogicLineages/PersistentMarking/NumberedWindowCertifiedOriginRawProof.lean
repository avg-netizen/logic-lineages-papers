module
public import LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginRawTargets
import LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginWitnessCodecProof
import LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginDirectProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginRawProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowFieldAlgorithm (unpack pack)
open NumberedWindowDirectAlgorithm (Witness readWitness direct directLists)
open NumberedWindowCertifiedOriginWitnessCodecTargets (packedWitness)
open NumberedWindowCertifiedOriginWitnessCodecProof (exact_PackedWitness)
open NumberedWindowCertifiedOriginDirectProof (exact_NumericOriginDirectCases)
open NumberedWindowCertifiedOriginRawTargets (chosenAccepts ExactChosenNumericRawOriginCases)
open NumberedWindowInternalDirectBoundaryGuardsTargets (ScalarFit)
open NumberedWindowInternalDirectCoreNumericTargets (PositiveFit)
open NumberedWindowInternalDirectCoreNumericProof (exact_NumericDCore)
open NumberedWindowInternalLiteralCountNumericChecks (exact_OriginalLiteralCountFit)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowAtomicRawStepFieldProof (unpackPacked)

private theorem packAndAccept (scalar : Program 1) (r : Program 3)
    (scalarTest : Nat → Bool) (positive : Nat → Nat → Nat → Bool)
    (sf : ScalarFit scalar scalarTest) (pf : PositiveFit r positive)
    (raw : Nat) (source target : List Nat) (w : Witness)
    (view : unpack raw = some source)
    (checked : directLists scalarTest positive source target w = true) :
    chosenAccepts scalar r raw (packedWitness w) (pack target) := by
  unfold chosenAccepts
  rw [exact_NumericDCore scalar r permutation scalarTest positive sf pf exact_OriginalLiteralCountFit]
  have certView : readWitness (packedWitness w) = some w := exact_PackedWitness w
  simp only [direct, view, unpackPacked, certView, checked] <;> rfl

theorem exact_ChosenNumericRawOriginCases : ExactChosenNumericRawOriginCases := by
  intro scalar r scalarTest positive sf pf rawLeft rawRight rawSource rawCert rawTarget
    left right source target leftView rightView sourceView targetView joined accepted
  unfold chosenAccepts at accepted
  rw [exact_NumericDCore scalar r permutation scalarTest positive sf pf exact_OriginalLiteralCountFit] at accepted
  cases certView : readWitness rawCert with
  | none =>
    simp only [direct, sourceView, targetView, certView] at accepted <;> contradiction
  | some w =>
    have checked : directLists scalarTest positive source target w = true := by
      cases h : directLists scalarTest positive source target w with
      | false =>
        simp only [direct, sourceView, targetView, certView, h] at accepted <;> contradiction
      | true => rfl
    rcases exact_NumericOriginDirectCases scalarTest positive left right source target w joined checked with
      ⟨l',wl,hl,jl⟩ | ⟨r',wr,hr,jr⟩ | ⟨l',r',wl,wr,hl,hr,jlr⟩
    · exact Or.inl ⟨l',wl,packAndAccept scalar r scalarTest positive sf pf rawLeft left l' wl leftView hl,jl⟩
    · exact Or.inr (Or.inl ⟨r',wr,
        packAndAccept scalar r scalarTest positive sf pf rawRight right r' wr rightView hr,jr⟩)
    · exact Or.inr (Or.inr ⟨l',r',wl,wr,
        packAndAccept scalar r scalarTest positive sf pf rawLeft left l' wl leftView hl,
        packAndAccept scalar r scalarTest positive sf pf rawRight right r' wr rightView hr,jlr⟩)

#print axioms exact_ChosenNumericRawOriginCases

end LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginRawProof
