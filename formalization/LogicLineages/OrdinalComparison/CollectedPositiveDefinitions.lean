module
public import LogicLineages.OrdinalComparison.ProfileCompilerDefinitions
public import LogicLineages.OrdinalComparison.RawNormalProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

/- Raw finite recursive dictionary trees for the one-variable source normal
form. Canonicality is a separate invariant, not a constructor premise. -/
mutual
  inductive CollectedPositiveNF where
    | mk : Nat → Nat → CollectedPositiveTags → CollectedPositiveNF
  inductive CollectedPositiveTags where
    | nil : CollectedPositiveTags
    | cons : NONote → CollectedPositiveNF → Nat → CollectedPositiveTags → CollectedPositiveTags
end

mutual
  def collectedPositiveEncode : CollectedPositiveNF → Nat
    | .mk c b tags => Nat.pair c (Nat.pair b (collectedTagsEncode tags))
  def collectedTagsEncode : CollectedPositiveTags → Nat
    | .nil => 0
    | .cons rho A a rest => 1 + Nat.pair
        (Nat.pair (rawNoteEncode rho.1) (collectedPositiveEncode A))
        (Nat.pair a (collectedTagsEncode rest))
end

/-- Code order is only a canonical storage order, never semantic value order. -/
def collectedTagKey (rho : NONote) (A : CollectedPositiveNF) : Nat :=
  Nat.pair (rawNoteEncode rho.1) (collectedPositiveEncode A)

mutual
  def collectedPositiveSupport : CollectedPositiveNF → Bool
    | .mk _ b tags => (b != 0) || collectedTagsSupport tags
  def collectedTagsSupport : CollectedPositiveTags → Bool
    | .nil => false
    | .cons _ A _ rest => collectedPositiveSupport A || collectedTagsSupport rest
end

mutual
  def collectedPositiveHeight : CollectedPositiveNF → Nat
    | .mk _ _ tags => collectedTagsHeight tags
  def collectedTagsHeight : CollectedPositiveTags → Nat
    | .nil => 0
    | .cons _ A _ rest => max (collectedPositiveHeight A + 1) (collectedTagsHeight rest)
end

mutual
  noncomputable def actualCollectedPositiveEval : CollectedPositiveNF → Nat → Nat
    | .mk c b tags, x => c + b*x + actualCollectedTagsEval tags x
  noncomputable def actualCollectedTagsEval : CollectedPositiveTags → Nat → Nat
    | .nil, _ => 0
    | .cons rho A a rest, x => a * actualProfileHead rho (actualCollectedPositiveEval A x) +
        actualCollectedTagsEval rest x
end

def collectedTagsKeysAbove (k : Nat) : CollectedPositiveTags → Prop
  | .nil => True
  | .cons rho A _ rest => k < collectedTagKey rho A ∧ collectedTagsKeysAbove k rest

mutual
  def CollectedPositiveValid : CollectedPositiveNF → Prop
    | .mk _ _ tags => CollectedTagsValid tags
  def CollectedTagsValid : CollectedPositiveTags → Prop
    | .nil => True
    | .cons rho A a rest => Order.IsSuccLimit rho.1.repr ∧ rho.1.repr < epsilonZero ∧
        CollectedPositiveValid A ∧ collectedPositiveSupport A=true ∧ 0<a ∧
        collectedTagsKeysAbove (collectedTagKey rho A) rest ∧ CollectedTagsValid rest
end

end LogicLineages.OrdinalComparison
