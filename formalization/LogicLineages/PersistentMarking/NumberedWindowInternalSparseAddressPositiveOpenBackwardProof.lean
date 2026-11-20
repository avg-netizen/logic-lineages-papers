module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenSideProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenMatchProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenFoldProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenGateProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBackwardProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult rawLeast)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseAddressPositive
open NumberedWindowInternalSparseAddressPositiveOpenTargets
open NumberedWindowInternalSparseAddressPositiveOpenTapeProof (args slotIntro acceptedRename)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (reportsCases)
open NumberedWindowInternalSparseAddressPositiveOpenSideProof (sideIntro)
open NumberedWindowInternalSparseAddressPositiveOpenMatchProof (introSame)
open NumberedWindowInternalSparseAddressPositiveOpenFoldProof (foldIntro)
open NumberedWindowInternalSparseAddressPositiveOpenGateProof (gateIntro)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem fromReports (cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (left cert right c t src dst : OTerm α)
    (read : Nonempty (Derivation body Γ (witnessData cv tv raw least left cert right c t src dst))) :
    Nonempty (Derivation body Γ (programGraph (addressPositive cv tv raw least) (suc z)
      (args left cert right))) := by
  obtain ⟨u⟩ := read
  let xs := args left cert right
  let l : Derivation body Γ (addressReport left c t src) := Derivation.conjunctionLeft u
  let r : Derivation body Γ (addressReport right c t dst) :=
    Derivation.conjunctionLeft (Derivation.conjunctionRight u)
  let valid := Derivation.conjunctionRight (Derivation.conjunctionRight u)
  let cv' : Nonempty (Derivation body Γ (unary cv (suc z) c)) := ⟨Derivation.conjunctionLeft valid⟩
  let tv' : Nonempty (Derivation body Γ (unary tv (suc z) t)) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight valid)⟩
  have leftCtx := slotIntro rawContext 0 c xs ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight l)⟩
  have rightCtx := slotIntro rawContext 2 c xs ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight r)⟩
  have leftTy := slotIntro rawResult 0 t xs
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight l))⟩
  have rightTy := slotIntro rawResult 2 t xs
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight r))⟩
  have leftClass := slotIntro rawLeast 0 src xs
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight l))⟩
  have rightClass := slotIntro rawLeast 2 dst xs
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight r))⟩
  have fold := foldIntro raw least xs c t src dst leftCtx leftTy leftClass rightClass
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight valid)⟩
  exact gateIntro cv tv raw least xs ⟨sideIntro cv tv 0 xs c t src ⟨l⟩ cv' tv',
    sideIntro cv tv 2 xs c t dst ⟨r⟩ cv' tv',
    introSame rawContext xs c leftCtx rightCtx,introSame rawResult xs t leftTy rightTy,fold⟩

theorem backward (cv tv : Program 1) (raw : Program 5) (least : Program 3) (left cert right : OTerm α)
    (reported : Nonempty (Derivation body Γ (someAddressPositive cv tv raw least left cert right))) :
    Nonempty (Derivation body Γ (programGraph (addressPositive cv tv raw least) (suc z)
      (args left cert right))) := by
  apply reportsCases cv tv raw least left cert right
    (programGraph (addressPositive cv tv raw least) (suc z) (args left cert right)) reported
  intro β j Δ c t src dst _ report
  rw [acceptedRename]
  exact fromReports cv tv raw least (left.relabel j) (cert.relabel j) (right.relabel j) c t src dst report

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBackwardProof
