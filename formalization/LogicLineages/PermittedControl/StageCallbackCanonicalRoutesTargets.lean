module
public import LogicLineages.PermittedControl.ActualCanonicalFundedTerminalTargets
public import LogicLineages.PermittedControl.ActualBoundedSignedRouteSemanticsTargets
public import LogicLineages.PermittedControl.ActualSelectedSignedRoutePacketTargets
public import LogicLineages.PermittedControl.ActualPaidSignedRouteReplayTargets

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackCanonicalRoutes
open OrdinalComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand encodeWeighted)
open ActualMixedRowLeadingAnnotations (NonlinearOperand)
open ActualCanonicalOperandGrouping (groupTyped)
open ActualCanonicalSymbolicZeroSuccessor (canonicalSuccessor)
open ActualCanonicalTerminalTruth (canonicalPacket)
open ActualCanonicalZeroTrace (CanonicalTrace CanonicalZeroWitness)
open ActualFullValueLabels (labels)
open ActualFullLabelPairGuards (Pair Answer)
open ActualFiniteFullValueGuards (pairs patterns compile Matches)
open ActualFullValueMaximalMetadata (maximalCoefficient)
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualSignedOrdinaryPairHigh (OrderTest)
open ActualPreparedSlotAppend (Packet)
open ActualSelectedSignedRoutePacket (Shape terminalPacket)
open ActualBoundedSignedRoutes (Tip Route PacketHolds RouteHolds prefixGuard)
open ActualBoundedSignedRouteSemantics (RunContext stateSyntax)
open ActualRankedNormalizationSyntax (extend)
open ActualReadChargeIteration (ReadState stateValue stateCharge)
open ActualFiniteGlobalTail (syntaxOf)
open ActualEffectiveTerminalSignBound (inputSignBoundCode)
open ActualSyntaxChargeBudget (syntaxBudget)
open ActualPaidSignedRouteReplay (LowerSetup replayMinimum SourceHolds)

/-- A nonlinear occurrence with nonzero grouped coefficient at the greatest
rank, read on the first-occurrence grouping of the literal term list. This
is a property of syntax only. -/
def CanonicalActive (top : Nat) (terms : List WeightedOperand) : Prop :=
  ∃ t ∈ groupTyped terms, t.1 ≠ 0 ∧ t.2.rank = top ∧ NonlinearOperand t.2

/-- Every ternary answer tape of the node's own pair width; `grouped` is
the already grouped term list. -/
def tapes (grouped : List WeightedOperand) : List (List Answer) :=
  patterns (pairs (labels grouped)).length

/-- The comparison guard of one answer tape on the grouped label order. -/
def guard (top : Nat) (grouped : List WeightedOperand) (a : List Answer) : Packet :=
  compile top (pairs (labels grouped)) a

noncomputable def linearRoute (top : Nat) (test : OrderTest) (positive : Bool) (s : SyntaxState) :
    Route :=
  ⟨[],.linear (canonicalPacket top s.constant s.terms test.test positive)⟩

noncomputable def signedRoute (top : Nat) (s : SyntaxState) (a : List Answer) : Route :=
  ⟨[guard top (groupTyped s.terms) a],.signed (maximalCoefficient (groupTyped s.terms) a)⟩

/-- A zero-coefficient tape continues only through its own symbolic
successor; a nonzero tape is a leaf carrying its coefficient. -/
noncomputable def branchRoutes (top : Nat) (s : SyntaxState) (next : SyntaxState → List Route)
    (a : List Answer) : List Route :=
  if maximalCoefficient (groupTyped s.terms) a = 0 then
    match canonicalSuccessor s.constant s.terms a with
    | none => []
    | some out => (next out).map (prefixGuard (guard top (groupTyped s.terms) a))
  else [signedRoute top s a]

open scoped Classical in
/-- Only stopped candidates are leaves: an inactive node contributes its
linear packet and has no children; an active node contributes one leaf per
nonzero tape and descends through zero tapes. A node all of whose tapes
continue contributes nothing by itself. -/
noncomputable def nodeRoutes (top : Nat) (test : OrderTest) (positive : Bool) (s : SyntaxState)
    (next : SyntaxState → List Route) : List Route :=
  if CanonicalActive top s.terms then
    (tapes (groupTyped s.terms)).flatMap (branchRoutes top s next)
  else [linearRoute top test positive s]

/-- Fuel counts zero edges only, as in the accepted route tree. -/
noncomputable def routes (top : Nat) (test : OrderTest) (positive : Bool) :
    Nat → SyntaxState → List Route
  | 0,s => nodeRoutes top test positive s (fun _ => [])
  | n+1,s => nodeRoutes top test positive s (routes top test positive n)

/-- The accepted run context together with the one extra payment the
canonical route needs: the static sign bound of the initial syntax. -/
structure CanonicalContext (f : Nat → Nat) (B : Nat) (baseline : Nat → Nat)
    (r top z : Nat) (initial : ReadState) : Prop where
  run : RunContext f B baseline r top z initial
  sign : inputSignBoundCode r initial.constant ((syntaxOf initial).map encodeWeighted) ≤ z

/-- What a holding guard certifies at a genuinely reached active node. -/
def RealBranch (f : Nat → Nat) (B : Nat) (baseline : Nat → Nat)
    (r top z : Nat) (s : ReadState) (a : List Answer) : Prop :=
  (maximalCoefficient (groupTyped (syntaxOf s)) a = 0 ∧ ∃ out : ReadState,
      CanonicalZeroWitness f B (extend baseline top z) r top s out a ∧
      canonicalSuccessor s.constant (syntaxOf s) a = some (stateSyntax out) ∧
      stateValue s = stateValue out ∧ stateCharge r out < stateCharge r s) ∨
  (maximalCoefficient (groupTyped (syntaxOf s)) a ≠ 0 ∧ ∀ (test : OrderTest) (positive : Bool),
    (test.test.atPolarity positive (stateValue s) ↔
      test.test.atPolarity positive (maximalCoefficient (groupTyped (syntaxOf s)) a)))

def ExactCanonicalRouteLayout : Prop :=
  ∀ (top n : Nat) (test : OrderTest) (positive : Bool) (s : SyntaxState) (route : Route),
    route ∈ routes top test positive n s ↔
      (¬ CanonicalActive top s.terms ∧ route = linearRoute top test positive s) ∨
      (CanonicalActive top s.terms ∧ ∃ a ∈ tapes (groupTyped s.terms),
        (maximalCoefficient (groupTyped s.terms) a ≠ 0 ∧ route = signedRoute top s a) ∨
        (maximalCoefficient (groupTyped s.terms) a = 0 ∧ ∃ k out, n = k+1 ∧
          canonicalSuccessor s.constant s.terms a = some out ∧
          ∃ tail ∈ routes top test positive k out,
            route = prefixGuard (guard top (groupTyped s.terms) a) tail))

/-- Shape only, for every emitted route, with no semantic hypothesis. -/
def ExactCanonicalRouteShape : Prop :=
  ∀ (top fuel : Nat) (test : OrderTest) (positive : Bool) (s : SyntaxState) (route : Route),
    route ∈ routes top test positive fuel s →
    (∀ p ∈ route.guards, Shape p) ∧ Shape (terminalPacket test positive route.tip)

/-- At one valuation the true answer tape of a pair list is unique. -/
def ExactMatchedAnswerUnique : Prop :=
  ∀ (f θ : Nat → Nat) (ps : List Pair) (a b : List Answer),
    Matches f θ ps a → Matches f θ ps b → a = b

def ExactCanonicalReachedLinear : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (baseline : Nat → Nat) (r top z : Nat) (initial : ReadState),
    CanonicalContext f B baseline r top z initial →
    ∀ (answers : List (List Answer)) (s : ReadState),
      CanonicalTrace f B (extend baseline top z) r top answers initial s →
      ¬ CanonicalActive top (syntaxOf s) →
      ∀ (test : OrderTest) (positive : Bool),
        (RouteHolds f baseline top z test positive (linearRoute top test positive (stateSyntax s)) ↔
          test.test.atPolarity positive (stateValue s))

/-- Guard exactness on the canonical label order at a genuinely reached
active node: a guard holds, with its own tied lower table at the shared
greatest value, exactly when its tape is the true comparison tape of the
successful reads; some guard holds; and a holding guard has the genuine
zero edge with the literal symbolic successor, or the requested signed
polarity of the row. -/
def ExactCanonicalReachedGuards : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (baseline : Nat → Nat) (r top z : Nat) (initial : ReadState),
    CanonicalContext f B baseline r top z initial →
    ∀ (answers : List (List Answer)) (s : ReadState),
      CanonicalTrace f B (extend baseline top z) r top answers initial s →
      CanonicalActive top (syntaxOf s) →
      (∀ a ∈ tapes (groupTyped (syntaxOf s)),
        (PacketHolds f baseline top z (guard top (groupTyped (syntaxOf s)) a) ↔
          Matches f (Function.update baseline top z)
            (pairs (labels (groupTyped (syntaxOf s)))) a)) ∧
      (∃ a ∈ tapes (groupTyped (syntaxOf s)),
        PacketHolds f baseline top z (guard top (groupTyped (syntaxOf s)) a)) ∧
      ∀ a ∈ tapes (groupTyped (syntaxOf s)),
        PacketHolds f baseline top z (guard top (groupTyped (syntaxOf s)) a) →
          RealBranch f B baseline r top z s a

def ExactCanonicalRouteSoundness : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (baseline : Nat → Nat) (r top z : Nat) (initial : ReadState),
    CanonicalContext f B baseline r top z initial →
    ∀ (test : OrderTest) (positive : Bool) (fuel : Nat) (answers : List (List Answer))
      (s : ReadState),
      CanonicalTrace f B (extend baseline top z) r top answers initial s →
      ∀ route ∈ routes top test positive fuel (stateSyntax s),
        RouteHolds f baseline top z test positive route →
          test.test.atPolarity positive (stateValue s)

def ExactCanonicalRouteCompleteness : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (baseline : Nat → Nat) (r top z : Nat) (initial : ReadState),
    CanonicalContext f B baseline r top z initial →
    ∀ (test : OrderTest) (positive : Bool) (fuel : Nat) (answers : List (List Answer))
      (s : ReadState),
      CanonicalTrace f B (extend baseline top z) r top answers initial s →
      stateCharge r s ≤ fuel →
      test.test.atPolarity positive (stateValue s) →
        ∃ route ∈ routes top test positive fuel (stateSyntax s),
          RouteHolds f baseline top z test positive route

def ExactCanonicalSufficientRoutes : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (baseline : Nat → Nat) (r top z : Nat) (initial : ReadState),
    CanonicalContext f B baseline r top z initial →
    ∀ (test : OrderTest) (positive : Bool),
      (test.test.atPolarity positive (stateValue initial) ↔
        ∃ route ∈ routes top test positive (syntaxBudget r (syntaxOf initial)) (stateSyntax initial),
          RouteHolds f baseline top z test positive route)

/-- Both directions for one signed source syntax across the replayed
greatest value, under the accepted lower setup and replay minimum plus the
static sign payment. The right side mentions syntax and packets only. -/
def ExactCanonicalRoutesAcrossReplay : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (r top : Nat) (baseline : Nat → Nat) (s : SyntaxState), LowerSetup B r top baseline s →
    ∀ (z : Nat), replayMinimum B r top baseline s ≤ z →
    inputSignBoundCode r s.constant (s.terms.map encodeWeighted) ≤ z →
    ∀ (test : OrderTest) (positive : Bool),
      (SourceHolds f (Function.update baseline top z) s test positive ↔
        ∃ path ∈ routes top test positive (syntaxBudget r s.terms) s,
          RouteHolds f baseline top z test positive path)

def FullStageCallbackCanonicalRoutes : Prop :=
  ExactCanonicalRouteLayout ∧ ExactCanonicalRouteShape ∧ ExactMatchedAnswerUnique ∧
    ExactCanonicalReachedLinear ∧ ExactCanonicalReachedGuards ∧
    ExactCanonicalRouteSoundness ∧ ExactCanonicalRouteCompleteness ∧
    ExactCanonicalSufficientRoutes ∧ ExactCanonicalRoutesAcrossReplay

end LogicLineages.PermittedControl.StageCallbackCanonicalRoutes
