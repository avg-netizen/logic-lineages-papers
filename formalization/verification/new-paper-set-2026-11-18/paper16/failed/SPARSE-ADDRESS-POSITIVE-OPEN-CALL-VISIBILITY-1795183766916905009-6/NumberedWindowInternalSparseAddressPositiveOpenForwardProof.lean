module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenSelectorProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenSideProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenMatchProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenFoldProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenGateProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenForwardProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseAddressPositive
open NumberedWindowInternalSparseAddressPositiveOpenTargets
open NumberedWindowInternalSparseAddressPositiveOpenTapeProof (args acceptedRename)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (reportRename supply)
open NumberedWindowInternalSparseAddressPositiveOpenSelectorProof (Observations choose)
open NumberedWindowInternalSparseAddressPositiveOpenSideProof (sideRead align)
open NumberedWindowInternalSparseAddressPositiveOpenMatchProof (readSame)
open NumberedWindowInternalSparseAddressPositiveOpenFoldProof (foldRead)
open NumberedWindowInternalSparseAddressPositiveOpenGateProof (gateRead)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem afterSelectors (cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (left cert right : OTerm α) (ys : Fin 6 → OTerm α)
    (accepted : Nonempty (Derivation body Γ (programGraph (addressPositive cv tv raw least) (suc z)
      (args left cert right))))
    (observed : Observations body Γ (args left cert right) ys) :
    Nonempty (Derivation body Γ (someAddressPositive cv tv raw least left cert right)) := by
  let xs := args left cert right
  obtain ⟨l,r,c,t,f⟩ := gateRead cv tv raw least xs accepted
  obtain ⟨lRep,cValid,tValid⟩ := sideRead cv tv 0 xs (ys 0) (ys 1) (ys 2) l
    (observed 0) (observed 1) (observed 2)
  obtain ⟨rRep,_,_⟩ := sideRead cv tv 2 xs (ys 3) (ys 4) (ys 5) r
    (observed 3) (observed 4) (observed 5)
  obtain ⟨ce⟩ := readSame rawContext xs (ys 0) (ys 3) (observed 0) (observed 3) c
  obtain ⟨te⟩ := readSame rawResult xs (ys 1) (ys 4) (observed 1) (observed 4) t
  have rr := align right (ys 3) (ys 4) (ys 0) (ys 1) (ys 5) ⟨symm ce⟩ ⟨symm te⟩ rRep
  have fold := foldRead raw least xs (ys 0) (ys 1) (ys 2) (ys 5)
    (observed 0) (observed 1) (observed 2) (observed 5) f
  obtain ⟨lrep⟩ := lRep
  obtain ⟨rrep⟩ := rr
  obtain ⟨pc⟩ := cValid
  obtain ⟨pt⟩ := tValid
  obtain ⟨pf⟩ := fold
  have result : Nonempty (Derivation body Γ (witnessData cv tv raw least left cert right
      (ys 0) (ys 1) (ys 2) (ys 5))) :=
    ⟨Derivation.conjunctionIntroduction lrep (Derivation.conjunctionIntroduction rrep
      (Derivation.conjunctionIntroduction pc (Derivation.conjunctionIntroduction pt pf)))⟩
  exact supply cv tv raw least left cert right (ys 0) (ys 1) (ys 2) (ys 5) result

theorem forward (cv tv : Program 1) (raw : Program 5) (least : Program 3) (left cert right : OTerm α)
    (accepted : Nonempty (Derivation body Γ (programGraph (addressPositive cv tv raw least) (suc z)
      (args left cert right)))) :
    Nonempty (Derivation body Γ (someAddressPositive cv tv raw least left cert right)) := by
  apply choose left cert right (someAddressPositive cv tv raw least left cert right)
  intro β j Δ ys hJ read
  rw [reportRename]
  have h := renameInto accepted j Δ hJ
  rw [acceptedRename] at h
  exact afterSelectors cv tv raw least (left.relabel j) (cert.relabel j) (right.relabel j) ys h read

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenForwardProof
