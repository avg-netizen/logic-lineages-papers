module
public import LogicLineages.PermittedControl.OriginalMixedTerminalTestTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMixedTerminalFiniteLow
open ArbitraryHeadSharedWire (Valuation)
open ArbitraryHeadWireList (Agrees)
open OriginalMixedGateSequential (Gate Topological run LeavesExternal)
open OriginalMixedGateNormalization (collapseEntries normalized Holds)
open OriginalMixedTerminalTest (Test testCeiling)

abbrev Row := Nat × Option (Valuation × Bool)

def lowCeiling (known : List Nat) (rank : Nat) (p : Test) : Nat :=
  known.foldr max (max rank (testCeiling p))

noncomputable def result (f : Nat → Nat) (base : Valuation) (rank a : Nat)
    (gates : List Gate) (p : Test) : Option (Valuation × Bool) :=
  (run f (Function.update base rank a) gates).map (fun final => (final,p.answer final))

/-- Enumerate every original value below the supplied bound, including
failed states and negative tests, in original rank-value order. -/
noncomputable def table (f : Nat → Nat) (base : Valuation) (rank bound : Nat)
    (gates : List Gate) (p : Test) : List Row :=
  (List.range bound).map (fun a => (a,result f base rank a gates p))

def Row.accepts (positive : Bool) (row : Row) : Bool :=
  match row.2 with
  | none => false
  | some (_,actual) => actual == positive

noncomputable def anyPolarity (f : Nat → Nat) (base : Valuation) (rank bound : Nat)
    (gates : List Gate) (p : Test) (positive : Bool) : Bool :=
  (table f base rank bound gates p).any (Row.accepts positive)

/-- Keep the positive normalized graph and exact external ties outside
either test polarity. Even unused explicitly known external names are
protected by the separate numeric ceiling in the hidden normalization. -/
def ProjectedAt (f : Nat → Nat) (base : Valuation) (known : List Nat)
    (rank a : Nat) (gates : List Gate) (p : Test) (final : Valuation) (positive : Bool) : Prop :=
  let ext := Function.update base rank a
  let ceiling := lowCeiling known rank p
  LeavesExternal gates ext final ∧ final rank = a ∧
    ∃ lifted : Valuation,
      Holds f lifted (normalized ceiling gates) ∧ Agrees (collapseEntries ceiling gates) final lifted ∧
      (∀ name ∈ known, lifted name = ext name) ∧ p.atPolarity positive lifted

def ExactFiniteTableLayout : Prop :=
  ∀ (f : Nat → Nat) (base : Valuation) (rank bound : Nat) (gates : List Gate) (p : Test),
    (table f base rank bound gates p).map Prod.fst = List.range bound ∧
      ∀ (a : Nat) (hit : Option (Valuation × Bool)),
        (a,hit) ∈ table f base rank bound gates p ↔ a < bound ∧ hit = result f base rank a gates p

def ExactOriginalFiniteLowRows : Prop :=
  ∀ (f : Nat → Nat) (known : List Nat) (gates : List Gate), Topological known gates →
    ∀ (base : Valuation) (rank bound : Nat), rank ∈ known → ∀ (p : Test), p.Admitted →
      (∀ a : Nat, (a,none) ∈ table f base rank bound gates p ↔
        a < bound ∧ run f (Function.update base rank a) gates = none) ∧
      ∀ (a : Nat) (final : Valuation) (positive : Bool),
        (a,some (final,positive)) ∈ table f base rank bound gates p ↔
          a < bound ∧ ProjectedAt f base known rank a gates p final positive

def ExactOriginalFiniteLowPolarity : Prop :=
  ∀ (f : Nat → Nat) (known : List Nat) (gates : List Gate), Topological known gates →
    ∀ (base : Valuation) (rank bound : Nat), rank ∈ known → ∀ (p : Test), p.Admitted →
      ∀ positive : Bool, anyPolarity f base rank bound gates p positive = true ↔
        ∃ a < bound, ∃ final : Valuation, ProjectedAt f base known rank a gates p final positive

def FullOriginalMixedTerminalFiniteLow : Prop :=
  ExactFiniteTableLayout ∧ ExactOriginalFiniteLowRows ∧ ExactOriginalFiniteLowPolarity

end LogicLineages.PermittedControl.OriginalMixedTerminalFiniteLow
