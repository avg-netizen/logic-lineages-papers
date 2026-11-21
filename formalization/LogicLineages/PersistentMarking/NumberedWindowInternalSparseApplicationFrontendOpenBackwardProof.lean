module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenBindingProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenCallProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenBackwardProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeParsedEmitter
  (addressGood arrowGood rawContext rawResult rawLeast rawDomain rawCodomain)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressReports arrowReports)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph3Rename)
open NumberedWindowInternalSparseAddressPositiveOpenTapeProof (slotIntro)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore applicationGuard)
open NumberedWindowInternalSparseApplicationFrontendTargets (applicationReport parsedApplicationInputs)
open NumberedWindowInternalSparseApplicationFrontendOpenGateProof (G args makeCore makeGuard)
open NumberedWindowInternalSparseApplicationFrontendOpenCallProof (makeCompare makeOutput)
open NumberedWindowInternalSparseApplicationFrontendOpenBindingProof (row someRow rowCases)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem fromRow (least : Program 3) (f u y c r d e fn arg : OTerm α)
    (reported : Nonempty (Derivation body Γ (row least f u y c r d e fn arg))) :
    G body Γ (applicationCore least) (args f u y) := by
  obtain ⟨h⟩ := reported
  let xs := args f u y
  have observed : Derivation body Γ (parsedApplicationInputs f u c r d e fn arg) :=
    Derivation.conjunctionLeft h
  have a := Derivation.conjunctionRight observed
  have b := Derivation.conjunctionRight a
  have k := Derivation.conjunctionRight b
  have l : Derivation body Γ (addressReports f c r fn) := Derivation.conjunctionLeft k
  have p := Derivation.conjunctionRight k
  have uFields : Derivation body Γ (addressReports u c d arg) := Derivation.conjunctionLeft p
  have arrow : Derivation body Γ (arrowReports f d e) := Derivation.conjunctionLeft (Derivation.conjunctionRight p)
  have lf := slotIntro rawContext 0 c xs ⟨Derivation.conjunctionLeft l⟩
  have rf := slotIntro rawContext 1 c xs ⟨Derivation.conjunctionLeft uFields⟩
  have ad := slotIntro rawDomain 0 d xs ⟨Derivation.conjunctionLeft arrow⟩
  have ud := slotIntro rawResult 1 d xs ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight uFields)⟩
  have ae := slotIntro rawCodomain 0 e xs ⟨Derivation.conjunctionRight arrow⟩
  have fc := slotIntro rawLeast 0 fn xs ⟨Derivation.conjunctionRight (Derivation.conjunctionRight l)⟩
  have uc := slotIntro rawLeast 1 arg xs ⟨Derivation.conjunctionRight (Derivation.conjunctionRight uFields)⟩
  exact makeCore least xs
    ⟨slotIntro addressGood 0 (suc z) xs ⟨Derivation.conjunctionLeft observed⟩,
      slotIntro addressGood 1 (suc z) xs ⟨Derivation.conjunctionLeft a⟩,
      slotIntro arrowGood 0 (suc z) xs ⟨Derivation.conjunctionLeft b⟩,
      makeCompare rawContext rawContext xs c lf rf,
      makeCompare rawDomain rawResult xs d ad ud,
      makeOutput least xs c d e fn arg lf ad ae fc uc ⟨Derivation.conjunctionRight h⟩⟩

private theorem coreBackward (least : Program 3) (f u y : OTerm α)
    (given : Nonempty (Derivation body Γ (someRow least f u y))) :
    G body Γ (applicationCore least) (args f u y) := by
  apply rowCases least f u y (programGraph (applicationCore least) (suc z) ![f,u,y]) given
  intro β j Δ c r d e fn arg _ seen
  rw [graph3Rename,sucRelabel,zRelabel]
  exact fromRow least (f.relabel j) (u.relabel j) (y.relabel j) c r d e fn arg seen

theorem backward (i : Program 1) (least : Program 3) (f u y : OTerm α)
    (reported : Nonempty (Derivation body Γ (applicationReport i least f u y))) :
    G body Γ (applicationGuard i least) (args f u y) := by
  obtain ⟨h⟩ := reported
  have rest := Derivation.conjunctionRight h
  have core := coreBackward least f u y ⟨Derivation.conjunctionRight rest⟩
  exact makeGuard i least f u y ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionLeft rest⟩ core

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenBackwardProof
