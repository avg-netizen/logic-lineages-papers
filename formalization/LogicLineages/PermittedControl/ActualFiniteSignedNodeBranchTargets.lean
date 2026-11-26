module
public import LogicLineages.PermittedControl.ActualRankedNormalizationSyntaxTargets
public import LogicLineages.PermittedControl.ActualFullValueMaximalMetadataTargets
public import LogicLineages.PermittedControl.ActualReadChargeIterationTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFiniteSignedNodeBranch
open OrdinalComparison FieldComparison PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open MixedSameRankResidue (WeightedOperand)
open ActualRankedNormalizationSyntax (normalizedTerms LowerStrict AboveLower extend)
open ActualFullValueLabels (Label labels)
open ActualFullLabelPairGuards (Answer)
open ActualFiniteFullValueGuards (pairs patterns compile ReadyFamily PaidFamily)
open ActualFullValueMaximalMetadata (maximalCoefficient)
open ActualMixedRowLeadingAnnotations (CountTailReady NonlinearOperand)
open ActualMixedRowLeadingSum (rowCutoffCode)
open ActualZeroClassReplacement (Read liftedReads)
open ActualWeightedReadNormalization (normalizeReads)
open ActualZeroClassCommonTail (prefixLabels commonTail)
open ActualReadChargeIteration (ReadState ZeroEdge NonzeroTerminal stateValue)
open ActualPreparedSlotAppend (Packet)

noncomputable def nodeLabels (raw : List WeightedOperand) : List Label :=
  labels (normalizedTerms raw)

noncomputable def nodePattern (raw : List WeightedOperand) : List (List Answer) :=
  patterns (pairs (nodeLabels raw)).length

noncomputable def nodePacket (raw : List WeightedOperand) (top : Nat) (a : List Answer) : Packet :=
  compile top (pairs (nodeLabels raw)) a

noncomputable def nodeCoefficient (raw : List WeightedOperand) (a : List Answer) : Int :=
  maximalCoefficient (normalizedTerms raw) a

def StaticActive (top : Nat) (raw : List WeightedOperand) : Prop :=
  ∃ t ∈ normalizedTerms raw, t.1 ≠ 0 ∧ t.2.rank = top ∧ NonlinearOperand t.2

def StaticGuards (B : Nat) (θ : Nat → Nat) (raw : List WeightedOperand) : Prop :=
  let terms := normalizedTerms raw
  (∀ t ∈ terms, t.1 ≠ 0 → CountTailReady θ t.2) ∧
  ∀ label ∈ prefixLabels terms, commonTail B terms ≤ θ label.rank

def NodeResult (f : Nat → Nat) (B : Nat) (θ : Nat → Nat) (r top z : Nat)
    (source : ReadState) (raw : List WeightedOperand) (a : List Answer) : Prop :=
  let coef := nodeCoefficient raw a
  (coef = 0 ∧ ∃ out : ReadState, ZeroEdge f B θ r top source out) ∨
  (coef ≠ 0 ∧
    (∃ xs, normalizeReads f θ source.reads = some xs ∧ NonzeroTerminal f θ top source xs) ∧
    (rowCutoffCode source.constant ((normalizedTerms raw).map MixedSameRankResidue.encodeWeighted) ≤ z →
      (0 < stateValue source ↔ 0 < coef) ∧
      (stateValue source < 0 ↔ coef < 0) ∧
      (0 ≤ stateValue source ↔ 0 < coef) ∧ stateValue source ≠ 0))

/-- A source-static finite branch guards a concrete actual nonlinear
node at every paid greatest update. Short/identity cleanup and actual
strict charge stay on the existing one-step witness. No syntax for the
zero successor, or proof of all future node tails, is supplied here. -/
def ExactFiniteSignedNodeBranch : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (r top : Nat) (constant : Int) (raw : List WeightedOperand),
    LowerStrict ρ top →
    (∀ t ∈ raw, t.2.rank < r ∧ t.2.rank ≤ top) →
    StaticActive top raw → ReadyFamily B ρ top (nodeLabels raw) →
    ∀ a ∈ nodePattern raw,
      let q := nodePacket raw top a
      PreparedInput q.1 q.2 ∧
      (∃ ν : Nat → Nat, PreparedTableTied f top ρ q.1 ν) ∧
      ∀ (ν : Nat → Nat), PreparedTableTied f top ρ q.1 ν →
        ∀ z : Nat, AboveLower ρ top z → PaidFamily B ρ top z (nodeLabels raw) →
          let θ := extend ρ top z
          StaticGuards B θ raw →
          ∀ rs : List Read, rs.map Prod.fst = raw →
            liftedReads f (Function.update ρ top z) rs →
            q.2.eval (Function.update ν 0 z) →
            NodeResult f B θ r top z ⟨constant,rs⟩ raw a

end LogicLineages.PermittedControl.ActualFiniteSignedNodeBranch
