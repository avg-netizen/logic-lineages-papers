module
public import LogicLineages.PermittedControl.ActualSymbolicZeroSuccessorTargets
public import LogicLineages.PermittedControl.ActualSyntaxLinearTerminalTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBoundedSignedRoutes
open OrdinalComparison FieldComparison PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open MixedSameRankResidue (WeightedOperand)
open ActualSymbolicZeroSuccessor (SyntaxState successor)
open ActualRankedNormalizationSyntax (normalizedTerms)
open ActualFiniteSignedNodeBranch (nodePattern nodePacket nodeCoefficient StaticActive)
open ActualFullLabelPairGuards (Answer)
open ActualSignedOrdinaryPairHigh (OrderTest)
open ActualPreparedSlotAppend (Packet)

inductive Tip where
  | linear (packet : Packet)
  | signed (coef : Int)

structure Route where
  guards : List Packet
  tip : Tip

def nonlinear : LowerOperand → Bool
  | .coordinate _ => false
  | .ordinary _ (.iterate n) => decide (0 < n)
  | .ordinary _ (.entry ..) | .count .. => true

def activeTest (top : Nat) (t : WeightedOperand) : Bool :=
  decide (t.1 ≠ 0 ∧ t.2.rank = top) && nonlinear t.2

noncomputable def active (top : Nat) (raw : List WeightedOperand) : Bool :=
  (normalizedTerms raw).any (activeTest top)

/-- Every guard on the chosen route gets its own actual correlated tied
lower table, all at the same original control and raw baseline. No
table belonging only to an unchosen successor is required to be live. -/
def PacketHolds (f baseline : Nat → Nat) (top z : Nat) (p : Packet) : Prop :=
  ∃ ν : Nat → Nat, PreparedTableTied f top baseline p.1 ν ∧ p.2.eval (Function.update ν 0 z)

def TipHolds (f baseline : Nat → Nat) (top z : Nat) (test : OrderTest) (positive : Bool) :
    Tip → Prop
  | .linear p => PacketHolds f baseline top z p
  | .signed coef => test.test.atPolarity positive coef

def RouteHolds (f baseline : Nat → Nat) (top z : Nat) (test : OrderTest) (positive : Bool)
    (route : Route) : Prop :=
  (∀ g ∈ route.guards, PacketHolds f baseline top z g) ∧ TipHolds f baseline top z test positive route.tip

def prefixGuard (g : Packet) (route : Route) : Route := ⟨g::route.guards,route.tip⟩

noncomputable def linearRoute (top : Nat) (test : OrderTest) (positive : Bool) (s : SyntaxState) : Route :=
  ⟨[],.linear (ActualSyntaxLinearTerminal.packet top s.constant s.terms test.test positive)⟩

noncomputable def signedRoute (top : Nat) (s : SyntaxState) (answer : List Answer) : Route :=
  ⟨[nodePacket s.terms top answer],.signed (nodeCoefficient s.terms answer)⟩

noncomputable def branchRoutes (top : Nat) (s : SyntaxState) (next : SyntaxState → List Route)
    (answer : List Answer) : List Route :=
  if nodeCoefficient s.terms answer = 0 then
    match successor s.constant s.terms answer with
    | none => []
    | some out => (next out).map (prefixGuard (nodePacket s.terms top answer))
  else [signedRoute top s answer]

noncomputable def nodeRoutes (top : Nat) (test : OrderTest) (positive : Bool) (s : SyntaxState)
    (next : SyntaxState → List Route) : List Route :=
  if active top s.terms then (nodePattern s.terms).flatMap (branchRoutes top s next)
  else [linearRoute top test positive s]

/-- Fuel counts allowed zero edges only. A nonzero or linear terminal is
still a candidate at zero fuel. Invalid candidate syntax is not a leaf. -/
noncomputable def routes (top : Nat) (test : OrderTest) (positive : Bool) :
    Nat → SyntaxState → List Route
  | 0,s => nodeRoutes top test positive s (fun _ => [])
  | n+1,s => nodeRoutes top test positive s (routes top test positive n)

def ExactActiveSyntax : Prop :=
  ∀ (top : Nat) (raw : List WeightedOperand), active top raw = true ↔ StaticActive top raw

def ExactTypedRouteLayout : Prop :=
  ∀ (top n : Nat) (test : OrderTest) (positive : Bool) (s : SyntaxState) (route : Route),
    route ∈ routes top test positive n s ↔
      (¬ StaticActive top s.terms ∧ route = linearRoute top test positive s) ∨
      (StaticActive top s.terms ∧ ∃ answer ∈ nodePattern s.terms,
        (nodeCoefficient s.terms answer ≠ 0 ∧ route = signedRoute top s answer) ∨
        (nodeCoefficient s.terms answer = 0 ∧ ∃ k out, n = k+1 ∧
          successor s.constant s.terms answer = some out ∧
          ∃ tail ∈ routes top test positive k out,
            route = prefixGuard (nodePacket s.terms top answer) tail))

def ExactPathLocalAvailability : Prop :=
  ∀ (f baseline : Nat → Nat) (top z : Nat) (test : OrderTest) (positive : Bool)
    (g : Packet) (tail : Route),
    RouteHolds f baseline top z test positive (prefixGuard g tail) ↔
      PacketHolds f baseline top z g ∧ RouteHolds f baseline top z test positive tail

def FullActualBoundedSignedRoutes : Prop :=
  ExactActiveSyntax ∧ ExactTypedRouteLayout ∧ ExactPathLocalAvailability

end LogicLineages.PermittedControl.ActualBoundedSignedRoutes
