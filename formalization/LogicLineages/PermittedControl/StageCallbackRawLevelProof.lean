module
public import LogicLineages.PermittedControl.StageCallbackRawLevelTargets
import LogicLineages.PermittedControl.StageCallbackLevelOrderProof
import LogicLineages.PermittedControl.ActualRawCanonicalNodeProof
import LogicLineages.PermittedControl.ActualRawCanonicalNodeMetadataProof
import LogicLineages.PermittedControl.ActualRawCanonicalAnswerTapesProof
import LogicLineages.PermittedControl.ActualRawSignedCleanupProof
import LogicLineages.PermittedControl.ActualSyntaxChargeBudgetCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackRawLevel
open OrdinalComparison
open PreparedProjection (LowerOperand PreparedPacketCode)
open RawPacketAlgebra (encodePacket)
open StageCallbackCanonicalRoutes (CanonicalActive tapes guard)
open StageCallbackLevelOrder (Entry stepOf children leafOf leaves level levelRoutes levelOrder
  stepOf_zero stepOf_nonzero leafOf_zero leafOf_nonzero children_active children_idle
  leaves_active leaves_idle)
open MixedSameRankResidue (WeightedOperand encodeWeighted)
open ActualMixedRowLeadingAnnotations (NonlinearOperand)
open ActualCanonicalOperandGrouping (encodeTerm groupRaw groupTyped)
open ActualCanonicalSymbolicZeroSuccessor (canonicalSuccessor)
open ActualCanonicalTerminalTruth (canonicalPacket)
open ActualRawComparisonCeiling (LabelCode encodeLabel)
open ActualRawCanonicalNodeMetadata (labelsCode tapeHighestCode exactRawCanonicalNodeCalibration)
open ActualRawCanonicalAnswerTapes (candidateTapes exactCanonicalAnswerPairs)
open ActualRawCanonicalNode (RawOutcome groupedCode exactRawCanonicalNode exactRawNodeBranches)
open ActualRawSignedStaticCeiling (RawSyntax encodeSyntax)
open ActualRawSignedCleanup (cleanupCode cleanupCalibration)
open ActualInitialSignedCountCleanup (cleanup)
open ActualSyntaxChargeBudget (syntaxBudget syntaxBudgetCode budgetCodeExact)
open ActualBitFamilyRawLayout (RawBitRow encodeBitRow)
open ActualFullValueLabels (labels)
open ActualFullLabelPairGuards (Answer)
open ActualFullValueMaximalMetadata (maximalCoefficient)
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualSignedOrdinaryPairHigh (OrderTest)
open ActualPreparedSlotAppend (Packet append)
open ActualBoundedSignedRoutes (Route nonlinear activeTest)
open ActualSelectedSignedRoutePacket (packet terminalPacket signedBit)

theorem filterMapTransport {α β γ δ : Type} (f : α → β) (g : α → Option γ)
    (g' : β → Option δ) (h : γ → δ) (l : List α)
    (pointwise : ∀ a, g' (f a) = (g a).map h) :
    (l.map f).filterMap g' = (l.filterMap g).map h := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hga : g a with
    | none =>
      have h1 : g' (f a) = none := by simp [pointwise,hga]
      rw [List.map_cons,List.filterMap_cons_none h1,List.filterMap_cons_none hga]
      exact ih
    | some c =>
      have h1 : g' (f a) = some (h c) := by simp [pointwise,hga]
      rw [List.map_cons,List.filterMap_cons_some h1,List.filterMap_cons_some hga,List.map_cons,ih]

theorem flatMapTransport {α β γ δ : Type} (f : α → β) (g : α → List γ) (g' : β → List δ)
    (h : γ → δ) (l : List α) (pointwise : ∀ a, g' (f a) = (g a).map h) :
    (l.map f).flatMap g' = (l.flatMap g).map h := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons,List.flatMap_cons,List.flatMap_cons,pointwise,ih,List.map_append]

theorem flatMapPointwise {α γ δ : Type} (g : α → List γ) (g' : α → List δ) (h : γ → δ)
    (l : List α) (pointwise : ∀ a, g' a = (g a).map h) :
    l.flatMap g' = (l.flatMap g).map h := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons,List.flatMap_cons,pointwise,ih,List.map_append]

theorem nonlinearExact (op : LowerOperand) : nonlinear op = true ↔ NonlinearOperand op := by
  cases op with
  | coordinate r => simp [nonlinear,NonlinearOperand]
  | count r l m => simp [nonlinear,NonlinearOperand]
  | ordinary r F =>
      cases F <;> simp [nonlinear,NonlinearOperand,SelectedNonlinearImageBounds.NonlinearField]

theorem exactRawActivity : ExactRawActivity := by
  intro top ts
  have cal : tapeHighestCode top (groupRaw (ts.map encodeWeighted)) =
      (groupTyped ts).any (activeTest top) := (exactRawCanonicalNodeCalibration top ts []).2.1
  rw [cal]
  simp only [CanonicalActive,List.any_eq_true,activeTest,Bool.and_eq_true,decide_eq_true_eq,
    nonlinearExact,and_assoc]

theorem tapesExact (ts : List WeightedOperand) :
    candidateTapes (groupRaw (ts.map encodeWeighted)) =
      (tapes (groupTyped ts)).map (List.map Answer.code) :=
  (exactCanonicalAnswerPairs.2 ts).2

theorem guardExact (R : Rendering) (hR : R.Exact) (top : Nat) (ts : List WeightedOperand)
    (a : List Answer) :
    R.guard top (labelsCode (groupRaw (ts.map encodeWeighted))) (a.map Answer.code) =
      encodePacket (guard top (groupTyped ts) a) := by
  have cal : labelsCode (groupRaw (ts.map encodeWeighted)) =
      (labels (groupTyped ts)).map encodeLabel := (exactRawCanonicalNodeCalibration top ts a).1
  rw [cal]
  exact hR.guard top (groupTyped ts) a

/-- The accepted raw node on an encoded syntax and tape: the typed
coefficient and the encoded typed successor. -/
theorem nodeOutExact (s : SyntaxState) (a : List Answer) :
    nodeOut (encodeSyntax s) (a.map Answer.code) =
      (maximalCoefficient (groupTyped s.terms) a,
        (canonicalSuccessor s.constant s.terms a).map encodeSyntax) := by
  have node := exactRawCanonicalNode true s.constant s.terms a
  have branch := (exactRawNodeBranches s.constant (s.terms.map encodeTerm)
    (a.map Answer.code)).2.1
  exact Option.some.inj (branch.symm.trans node)

theorem stepExact (R : Rendering) (hR : R.Exact) (top : Nat) (pre : List Packet)
    (s : SyntaxState) (a : List Answer) :
    stepOfCode R top (encodeEntry (pre,s)) (a.map Answer.code) =
      (stepOf top (pre,s) a).map encodeEntry := by
  have out := nodeOutExact s a
  have g := guardExact R hR top s.terms a
  by_cases zero : maximalCoefficient (groupTyped s.terms) a = 0
  · rw [stepOf_zero top pre s a zero]
    show (if (nodeOut (encodeSyntax s) (a.map Answer.code)).1 = 0 then
        (nodeOut (encodeSyntax s) (a.map Answer.code)).2.map
          (fun raw => (pre.map encodePacket ++
            [R.guard top (labelsCode (groupRaw (s.terms.map encodeWeighted)))
              (a.map Answer.code)],raw))
      else none) = _
    rw [out,g]
    show (if maximalCoefficient (groupTyped s.terms) a = 0 then
        ((canonicalSuccessor s.constant s.terms a).map encodeSyntax).map
          (fun raw => (pre.map encodePacket ++
            [encodePacket (guard top (groupTyped s.terms) a)],raw))
      else none) = _
    rw [if_pos zero]
    cases canonicalSuccessor s.constant s.terms a with
    | none => rfl
    | some o => simp [encodeEntry]
  · rw [stepOf_nonzero top pre s a zero]
    show (if (nodeOut (encodeSyntax s) (a.map Answer.code)).1 = 0 then _ else none) = none
    rw [out]
    exact if_neg zero

theorem childrenExact (R : Rendering) (hR : R.Exact) (top : Nat) (e : Entry) :
    childrenCode R top (encodeEntry e) = (children top e).map encodeEntry := by
  rcases e with ⟨pre,s⟩
  by_cases active : CanonicalActive top s.terms
  · rw [children_active top pre s active]
    show (if tapeHighestCode top (groupRaw (s.terms.map encodeWeighted)) = true then
        (candidateTapes (groupRaw (s.terms.map encodeWeighted))).filterMap
          (stepOfCode R top (encodeEntry (pre,s)))
      else []) = _
    rw [if_pos ((exactRawActivity top s.terms).mpr active),tapesExact s.terms]
    exact filterMapTransport (List.map Answer.code) (stepOf top (pre,s))
      (stepOfCode R top (encodeEntry (pre,s))) encodeEntry _
      (fun a => stepExact R hR top pre s a)
  · rw [children_idle top pre s active]
    show (if tapeHighestCode top (groupRaw (s.terms.map encodeWeighted)) = true then _
      else []) = []
    exact if_neg (fun h => active ((exactRawActivity top s.terms).mp h))

theorem joinExact (R : Rendering) (hR : R.Exact) (gs : List Packet) (tip : Packet) :
    (gs.map encodePacket).foldr R.append (encodePacket tip) =
      encodePacket (gs.foldr append tip) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    show R.append (encodePacket g) ((gs.map encodePacket).foldr R.append (encodePacket tip)) =
      encodePacket (append g (gs.foldr append tip))
    rw [ih,hR.append]

theorem signedBitExact (test : OrderTest) (c : Int) :
    signedBitCode (orderCode test) c = signedBit test c := by
  cases test <;> simp [signedBitCode,orderCode,signedBit]

theorem signedTipExact (test : OrderTest) (positive : Bool) (c : Int) :
    signedTipCode (orderCode test) positive c =
      encodePacket (terminalPacket test positive (.signed c)) := by
  unfold signedTipCode
  rw [signedBitExact]
  show (if (if positive then signedBit test c else !(signedBit test c)) = true then
      encodePacket ([],.truth) else encodePacket ([],.falsity)) =
    encodePacket ([],if (if positive then signedBit test c else !(signedBit test c)) = true
      then .truth else .falsity)
  generalize (if positive then signedBit test c else !(signedBit test c)) = b
  cases b <;> rfl

theorem leafExact (R : Rendering) (hR : R.Exact) (top : Nat) (test : OrderTest) (positive : Bool)
    (pre : List Packet) (s : SyntaxState) (a : List Answer) :
    leafOfCode R top (orderCode test) positive (encodeEntry (pre,s)) (a.map Answer.code) =
      (leafOf top (pre,s) a).map (fun route => encodePacket (packet test positive route)) := by
  have out := nodeOutExact s a
  have g := guardExact R hR top s.terms a
  by_cases zero : maximalCoefficient (groupTyped s.terms) a = 0
  · rw [leafOf_zero top pre s a zero]
    show (if (nodeOut (encodeSyntax s) (a.map Answer.code)).1 = 0 then none else _) = none
    rw [out]
    exact if_pos zero
  · rw [leafOf_nonzero top pre s a zero]
    show (if (nodeOut (encodeSyntax s) (a.map Answer.code)).1 = 0 then none
      else some ((pre.map encodePacket ++
          [R.guard top (labelsCode (groupRaw (s.terms.map encodeWeighted)))
            (a.map Answer.code)]).foldr R.append
        (signedTipCode (orderCode test) positive
          (nodeOut (encodeSyntax s) (a.map Answer.code)).1))) =
      some (encodePacket ((pre ++ [guard top (groupTyped s.terms) a]).foldr append
        (terminalPacket test positive (.signed (maximalCoefficient (groupTyped s.terms) a)))))
    rw [out,g]
    show (if maximalCoefficient (groupTyped s.terms) a = 0 then none
      else some ((pre.map encodePacket ++
          [encodePacket (guard top (groupTyped s.terms) a)]).foldr R.append
        (signedTipCode (orderCode test) positive (maximalCoefficient (groupTyped s.terms) a)))) = _
    rw [if_neg zero,signedTipExact]
    have joined : pre.map encodePacket ++ [encodePacket (guard top (groupTyped s.terms) a)] =
        (pre ++ [guard top (groupTyped s.terms) a]).map encodePacket := by simp
    rw [joined,joinExact R hR]

theorem leavesExact (R : Rendering) (hR : R.Exact) (top : Nat) (test : OrderTest)
    (positive : Bool) (e : Entry) :
    leavesCode R top (orderCode test) positive (encodeEntry e) =
      (leaves top test positive e).map (fun route => encodePacket (packet test positive route)) := by
  rcases e with ⟨pre,s⟩
  by_cases active : CanonicalActive top s.terms
  · rw [leaves_active top test positive pre s active]
    show (if tapeHighestCode top (groupRaw (s.terms.map encodeWeighted)) = true then
        (candidateTapes (groupRaw (s.terms.map encodeWeighted))).filterMap
          (leafOfCode R top (orderCode test) positive (encodeEntry (pre,s)))
      else _) = _
    rw [if_pos ((exactRawActivity top s.terms).mpr active),tapesExact s.terms]
    exact filterMapTransport (List.map Answer.code) (leafOf top (pre,s))
      (leafOfCode R top (orderCode test) positive (encodeEntry (pre,s)))
      (fun route => encodePacket (packet test positive route)) _
      (fun a => leafExact R hR top test positive pre s a)
  · rw [leaves_idle top test positive pre s active]
    show (if tapeHighestCode top (groupRaw (s.terms.map encodeWeighted)) = true then _
      else [(pre.map encodePacket).foldr R.append
        (R.linear top (encodeSyntax s) (orderCode test) positive)]) =
      [encodePacket (pre.foldr append
        (canonicalPacket top s.constant s.terms test.test positive))]
    rw [if_neg (fun h => active ((exactRawActivity top s.terms).mp h)),hR.linear,
      joinExact R hR]

theorem exactRawLevelEntries : ExactRawLevelEntries := by
  intro R hR top s n
  induction n with
  | zero => rfl
  | succ n ih =>
    show (levelCode R top (encodeSyntax s) n).flatMap (childrenCode R top) =
      ((level top s n).flatMap (children top)).map encodeEntry
    rw [ih]
    exact flatMapTransport encodeEntry (children top) (childrenCode R top) encodeEntry _
      (fun e => childrenExact R hR top e)

theorem exactRawSignedPackets : ExactRawSignedPackets := by
  intro R hR top test positive fuel s
  rw [List.map_map]
  exact flatMapPointwise (fun n => (level top s n).flatMap (leaves top test positive))
    (fun n => (levelCode R top (encodeSyntax s) n).flatMap
      (leavesCode R top (orderCode test) positive))
    (fun route => encodePacket (packet test positive route)) (List.range (fuel+1))
    (fun n => by
      rw [exactRawLevelEntries R hR top s n]
      exact flatMapTransport encodeEntry (leaves top test positive)
        (leavesCode R top (orderCode test) positive)
        (fun route => encodePacket (packet test positive route)) _
        (fun e => leavesExact R hR top test positive e))

theorem signedRowExact (R : Rendering) (hR : R.Exact) (r top : Nat) (c : Int)
    (ts : List WeightedOperand) (bit : Bool) (test : OrderTest) :
    signedCode R top (orderCode test) bit
        (syntaxBudgetCode r (cleanupCode (encodeSyntax ⟨c,ts⟩)).2)
        (cleanupCode (encodeSyntax ⟨c,ts⟩)) =
      (StageCallbackLevelOrder.alternatives r top (.signed ⟨cleanup ⟨c,ts⟩,test,bit⟩)).map
        encodePacket := by
  rw [cleanupCalibration]
  show signedCode R top (orderCode test) bit
      (syntaxBudgetCode r ((cleanup ⟨c,ts⟩).terms.map encodeWeighted))
      (encodeSyntax (cleanup ⟨c,ts⟩)) = _
  rw [budgetCodeExact.2]
  exact exactRawSignedPackets R hR top test bit (syntaxBudget r (cleanup ⟨c,ts⟩).terms)
    (cleanup ⟨c,ts⟩)

theorem exactRawRowPackets : ExactRawRowPackets := by
  intro R hR r top row
  rcases row with ⟨⟨test,c,ts⟩,bit⟩
  cases test with
  | equalZero => exact signedRowExact R hR r top c ts bit .equalZero
  | nonnegative => exact signedRowExact R hR r top c ts bit .nonnegative
  | positive => exact signedRowExact R hR r top c ts bit .positive
  | congruence m =>
    show [R.modular top m (encodeSyntax ⟨c,ts⟩) bit] =
      [encodePacket (ActualGreatestCongruenceRoute.packet top m ⟨c,ts⟩ bit)]
    rw [hR.modular]

end LogicLineages.PermittedControl.StageCallbackRawLevel
