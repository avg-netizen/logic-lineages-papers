module
public import LogicLineages.PermittedControl.ArbitraryFixedHeadCollapseTargets
public import LogicLineages.PermittedControl.AffineCollapseGraphCompositionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ArbitraryHeadSharedWire
open OrdinalComparison
open NaturalAffineGateGraph (Expression)

abbrev Valuation := Nat → Nat

def headCode (a : NONote) : Nat := rawNoteEncode a.1

def limitCode (a : NONote) : Nat := (rawSplitCode (headCode a)).unpair.1

def tailCode (a : NONote) : Nat := (rawSplitCode (headCode a)).unpair.2

def finiteExpression (a : NONote) (source : Nat) : Expression :=
  ((encodedFiniteValue (headCode a) : Int),[(1,source)])

def shiftedExpression (a : NONote) (source : Nat) : Expression :=
  (((rawNormCode (limitCode a) + tailCode a : Nat) : Int),[(1,source)])

def originalGraph (f : Nat → Nat) (a : NONote) (source output : Nat) (ν : Valuation) : Prop :=
  ArbitraryFixedHeadCollapse.read f (headCode a,ν source) = some (ν output)

def limitPair (f : Nat → Nat) (a : NONote) (source hidden output : Nat) (ν : Valuation) : Prop :=
  AffineCollapseGraphComposition.graph f (limitCode a) (shiftedExpression a source) hidden output ν

def ExactFiniteWire : Prop :=
  ∀ (f : Nat → Nat) (a : NONote), encodedFiniteTest (headCode a) = true →
    ∀ (source output : Nat) (ν : Valuation),
      originalGraph f a source output ν ↔ (NaturalAffineGateGraph.graph output
        (finiteExpression a source)).eval ν

/-- The only introduced graph wire is the original raw norm input of
the limit part. The source wire, output wire, and every other original
name keep exactly their supplied values. -/
def ExactInfiniteWire : Prop :=
  ∀ (f : Nat → Nat) (a : NONote), encodedFiniteTest (headCode a) = false →
    ∀ (source hidden output : Nat), hidden ≠ source → hidden ≠ output →
      ∀ ν : Valuation,
        (∀ t : Nat,
          limitPair f a source hidden output (Function.update ν hidden t) ↔
            originalGraph f a source output ν ∧
              t = (ArbitraryFixedHeadCollapse.transported (headCode a,ν source)).2) ∧
        ((∃! t : Nat, limitPair f a source hidden output (Function.update ν hidden t)) ↔
          originalGraph f a source output ν) ∧
        ∀ t n : Nat, n ≠ hidden → Function.update ν hidden t n = ν n

/-- Canonical transport includes the genuine domain of the original
limit reader and its exact original ordinal state. Interpretation as the
selected collapse is explicit, not presumed in the raw wire clauses. -/
def ExactTypedWireTransport : Prop :=
  (∀ (a : NONote) (u : Nat), encodedFiniteTest (headCode a) = false →
    let q := ArbitraryFixedHeadCollapse.transported (headCode a,u)
    ∃ lam : NONote,
      rawNoteEncode lam.1 = limitCode a ∧ Order.IsSuccLimit lam.1.repr ∧
      FixedHeadCollapseGraph.domain q ∧ lam.1.repr = actualLimitPart a.1.repr ∧
      tailCode a = actualTailPart a.1.repr ∧
      q.2 = actualOrdinalNorm lam.1.repr + (actualTailPart a.1.repr + u) ∧
      countInitial lam.1.repr q.2 = a.1.repr + (u : Ordinal)) ∧
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (a : NONote) (source output : Nat) (ν : Valuation),
      originalGraph f a source output ν ↔
        ν output = ParametricActualCollapse.collapseWith f (a.1.repr + (ν source : Ordinal))

def FullArbitraryHeadSharedWire : Prop :=
  ExactFiniteWire ∧ ExactInfiniteWire ∧ ExactTypedWireTransport

end LogicLineages.PermittedControl.ArbitraryHeadSharedWire
