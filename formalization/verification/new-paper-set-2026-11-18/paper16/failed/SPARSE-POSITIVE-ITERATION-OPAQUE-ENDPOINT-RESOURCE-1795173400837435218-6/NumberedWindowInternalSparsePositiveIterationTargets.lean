module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph stepGraph loopGraph)

/-- The same frozen six-input step ignores its prior fuel counter and
original seed fields, not the actual previous scratch state/context/type. -/
def OpenStepCoordinates : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3) (α : Type)
    (out prior ctx ty k initial certificate k' initial' certificate' : OTerm α),
    let a := stepGraph raw least out k prior ctx ty initial certificate
    let b := stepGraph raw least out k' prior ctx ty initial' certificate'
    Nonempty (Derivation body [] ((a.imp b) ⊓ (b.imp a)))

/-- At an actual earlier result, the exact successor-source graph both
produces and inverts the original selected step. -/
def OpenRecursorSuccessor : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3) (α : Type)
    (out prior fuel ctx ty initial certificate : OTerm α),
    let known := loopGraph raw least prior fuel ctx ty initial certificate
    let a := stepGraph raw least out fuel prior ctx ty initial certificate
    let b := loopGraph raw least out (suc fuel) ctx ty initial certificate
    Nonempty (Derivation body [] (known.imp ((a.imp b) ⊓ (b.imp a))))

/-- After one genuine step from the earlier initial scratch pair to the
new initial scratch pair, the symbolic remaining fuel is shared. No
native Nat.rec equation becomes a formula premise. -/
def OpenHeadFirstShift : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3) (α : Type)
    (out fuel ctx ty oldCurrent oldCertificate newCurrent newCertificate oldSeed newSeed : OTerm α),
    let transition := scratchGraph oldSeed oldCertificate oldCurrent ⊓
      (scratchGraph newSeed newCertificate newCurrent ⊓
        stepGraph raw least newSeed z oldSeed ctx ty oldCurrent oldCertificate)
    let a := loopGraph raw least out (suc fuel) ctx ty oldCurrent oldCertificate
    let b := loopGraph raw least out fuel ctx ty newCurrent newCertificate
    Nonempty (Derivation body [] (transition.imp ((a.imp b) ⊓ (b.imp a))))

/-- Fuel may increase by an arbitrary free ordinary-arithmetic term once
the actual loop output is a proved terminal scratch pair. -/
def OpenTerminalExtraFuel : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3) (α : Type)
    (out fuel extra ctx ty initial certificate current : OTerm α),
    let haveTerminal := loopGraph raw least out fuel ctx ty initial certificate ⊓ scratchGraph out z current
    let longer := loopGraph raw least out (OrdinaryArithmetic.addTerm fuel extra) ctx ty initial certificate
    Nonempty (Derivation body [] (haveTerminal.imp longer))

/-- Nil is genuinely stable for every symbolic fuel, at any raw context code. -/
def OpenTerminalNilLoop : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3) (α : Type)
    (out fuel ctx ty current : OTerm α),
    Nonempty (Derivation body [] ((scratchGraph out z current).imp
      (loopGraph raw least out fuel ctx ty current z)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationTargets
