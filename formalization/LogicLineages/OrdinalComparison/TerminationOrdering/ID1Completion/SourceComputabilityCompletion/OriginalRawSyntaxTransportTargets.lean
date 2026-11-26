module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportTargets
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- All-input machine calibration is independent of native source correctness
and does not imply any symbolic internal graph recurrence. -/
def ActualRawSyntaxTransitionCalibration : Prop :=
  ∀ (mode : Mode) (state : Nat),
  evaluate (transition mode) (List.Vector.ofFn ![state]) = transitionValue mode state

def ActualRawSyntaxEncodedTransition : Prop :=
  ∀ (mode : Mode) (state : State),
  transitionValue mode (encodeState state) = encodeState (stateStep mode state)

/-- The budget counts only ORIGINAL raw payloads. No child output size, type,
context, symbol bound or well-typedness premise is introduced. -/
def ActualRawSyntaxFuelBounds : Prop :=
  (∀ d k raw : Nat,
    evaluate fuel (List.Vector.ofFn ![d,k,raw]) = fuelValue raw ∧
    workWeight [visitValue d k raw] = fuelValue raw) ∧
  (∀ raw : Nat, arityValue raw = 1 → 1 + fuelValue (firstValue raw) + 1 ≤ fuelValue raw) ∧
  (∀ raw : Nat, arityValue raw = 2 →
    1 + fuelValue (firstValue raw) + fuelValue (secondValue raw) + 1 ≤ fuelValue raw)

def ActualRawSyntaxWorkDecrease : Prop :=
  ∀ (mode : Mode) (state : State), state.status = 1 → state.work ≠ [] →
    workWeight (stateStep mode state).work < workWeight state.work

def ActualRawSyntaxBoundedCalibration : Prop :=
  (∀ (mode : Mode) (count initial : Nat),
    evaluate (iterate mode) (List.Vector.ofFn ![count,initial]) = iterateValue mode count initial) ∧
  (∀ state : Nat, evaluate output (List.Vector.ofFn ![state]) = outputValue state) ∧
  (∀ (mode : Mode) (d k raw : Nat),
    evaluate (run mode) (List.Vector.ofFn ![d,k,raw]) = runValue mode d k raw ∧
    evaluate (fold mode) (List.Vector.ofFn ![d,k,raw]) = foldValue mode d k raw)

def ActualRawSyntaxNativeTermination : Prop :=
  ∀ (mode : Mode) (d k raw count : Nat), fuelValue raw ≤ count →
    ∃ out : Nat, iterateValue mode count (initialValue d k raw) = encodeState ⟨1, [], [out]⟩

/-- The actual bounded machine recursively handles EVERY structural raw tag.
In particular numbered base/extras and ordinary/list children are not leaves. -/
def ActualRawSyntaxNativeRecurrence : Prop :=
  ∀ (mode : Mode) (d k raw : Nat),
  (arityValue raw = 0 → foldValue mode d k raw = leafValue mode d k raw) ∧
  (arityValue raw = 1 → foldValue mode d k raw = rebuildValue mode raw
    (foldValue mode d (if tagValue raw = 1 then k + 1 else k) (firstValue raw)) 0) ∧
  (arityValue raw = 2 → foldValue mode d k raw = rebuildValue mode raw
    (foldValue mode d k (firstValue raw)) (foldValue mode d k (secondValue raw)))

/-- Exact ORIGINAL raw codeNumber, not Encodable.encode Code. These equations
are native calibration, kept separate from all internal proof obligations. -/
def ActualRawSyntaxCodeCalibration : Prop :=
  (∀ (n cutoff : Nat) (q : Code (Fin n)),
    evaluate shiftRaw (List.Vector.ofFn ![cutoff,codeNumber q]) =
      codeNumber (NumberedAuxiliaryShift.shiftCode cutoff q)) ∧
  (∀ (n cutoff : Nat) (sigma : Ty) (q : Code (Fin n)),
    evaluate eraseRaw (List.Vector.ofFn ![typeNumber sigma,cutoff,codeNumber q]) =
      codeNumber (eraseCode sigma cutoff q)) ∧
  (∀ (n : Nat) (q : Code (Fin n)),
    evaluate variableRankRaw (List.Vector.ofFn ![codeNumber q]) = codeVariableCount q)

/-- Typed correspondence uses the actual existing renaming/substitution, with
protected binders and all literal variable occurrences retained. -/
def ActualRawSyntaxTypedCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (binders Gamma : List Ty) (sigma tau : Ty),
  (∀ q : AuxTerm (Fin n) arity (binders ++ Gamma) tau,
    evaluate shiftRaw (List.Vector.ofFn ![binders.length,codeNumber (termCode q)]) =
      codeNumber (termCode (rename q (NumberedAuxiliaryShift.prefixWeakening binders Gamma sigma)))) ∧
  (∀ q : AuxTerm (Fin n) arity (binders ++ sigma :: Gamma) tau,
    evaluate eraseRaw (List.Vector.ofFn ![typeNumber sigma,binders.length,codeNumber (termCode q)]) =
      codeNumber (termCode (substitute q (prefixErasure binders Gamma sigma)))) ∧
  (∀ q : AuxTerm (Fin n) arity Gamma tau,
    evaluate variableRankRaw (List.Vector.ofFn ![codeNumber (termCode q)]) =
      NumberedVariableCount.variableCount q)

/-- With the declared unknown-tag identity leaves and total pair selectors,
cancellation is specified on ALL raw naturals. No native typed-code domain is
silently exchanged for the broader internal arithmetic domain. -/
def ActualRawSyntaxNativeCancellation : Prop :=
  ∀ d k raw : Nat,
    evaluate eraseRaw (List.Vector.ofFn ![d,k,evaluate shiftRaw (List.Vector.ofFn ![k,raw])]) = raw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportTargets
