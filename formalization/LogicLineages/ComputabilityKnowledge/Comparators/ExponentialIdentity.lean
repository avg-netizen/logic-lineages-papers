module

public import LogicLineages.ComputabilityKnowledge.ExponentialIdentity

@[expose] public section

/-! Exact full source N4 target, paper02 thm:identity. Every positive tuple,
actual source grammar/depth, original finite maps, exact literal parser
domain, and computed positive countervaluation are retained. Uniformity is
proved for the explicit option-valued programs, not a classical Decidable
instance or assumed normalizer-height coherence. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.ExponentialIdentity

open PositiveExpression ExponentialNormalForm ExponentialHereditaryCodec
open ExponentialNormalizer ExponentialNormalizerProgram CircuitReduction
open FiniteComparisonEnumeration RayFamilyClosure
open LogicLineages.ComputabilityKnowledge.ExponentialIdentity

def OriginalFormCompleteness : Prop :=
  ∀ (d h : Nat) (f g : Form d h), WellFormed h f → WellFormed h g →
    ((∀ ρ : Fin d → PosNat, value h f (fun i => (ρ i : Nat)) =
      value h g (fun i => (ρ i : Nat))) ↔ f = g)

def SourceN4 : Prop :=
  ∀ (d : Nat) (a b : Expr (Fin d)), ExtensionalEq a b ↔
    normalizeAt a (max a.depth b.depth) = normalizeAt b (max a.depth b.depth)

def RawInputCoverage : Prop :=
  ∀ (d : Nat) (raw : List Nat), (decodeExpr d raw).isSome = true ↔
    ∃ e : Expr (Fin d), raw = encodeExpr (e.rename Fin.val)

def LiftedNormalization : Prop :=
  ∀ (d : Nat) (e : Expr (Fin d)) (H : Nat), e.depth ≤ H →
    ∃ n, normalizeCode d (encodeExpr (e.rename Fin.val)) = some (e.depth, n) ∧
      CodeCanonical d H (liftCode d H (e.depth, n)) ∧
      formDecode d H (liftCode d H (e.depth, n)) = normalizeAt e H

def ExactRawDomain : Prop :=
  ∀ (d : Nat) (a b : List Nat),
    (decisionCode d a b).isSome = ((decodeExpr d a).isSome && (decodeExpr d b).isSome) ∧
    ((separatorCode d a b).isSome = true ↔ decisionCode d a b = some false)

def SourceDecision : Prop :=
  ∀ (d : Nat) (a b : Expr (Fin d)),
    (decisionCode d (encodeExpr (a.rename Fin.val)) (encodeExpr (b.rename Fin.val)) =
      some true ↔ ExtensionalEq a b) ∧
    (decisionCode d (encodeExpr (a.rename Fin.val)) (encodeExpr (b.rename Fin.val)) =
      some false ↔ ¬ExtensionalEq a b)

def ComputedPositiveSeparator : Prop :=
  ∀ (d : Nat) (a b : Expr (Fin d)), ¬ExtensionalEq a b →
    ∃ (xs : List Nat) (hpos : ∀ i : Fin d, 0 < xs.getD i.val 0),
      separatorCode d (encodeExpr (a.rename Fin.val)) (encodeExpr (b.rename Fin.val)) = some xs ∧
      xs.length = d ∧ a.eval (positiveTuple d xs hpos) ≠ b.eval (positiveTuple d xs hpos)

def ActualUniformPrograms : Prop :=
  Primrec (fun p : Nat × List Nat × List Nat => normalInputs p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × (HeightCode × HeightCode) => sameCode p.1 p.2) ∧
  Primrec (fun p : Nat × List Nat × List Nat => decisionCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × List Nat × List Nat => separatorCode p.1 p.2.1 p.2.2)

def Target : Prop := OriginalFormCompleteness ∧ SourceN4 ∧ RawInputCoverage ∧
  LiftedNormalization ∧ ExactRawDomain ∧ SourceDecision ∧ ComputedPositiveSeparator ∧
  ActualUniformPrograms

end LogicLineages.ComputabilityKnowledge.Comparators.ExponentialIdentity
