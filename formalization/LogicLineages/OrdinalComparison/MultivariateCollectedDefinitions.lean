module
public import LogicLineages.OrdinalComparison.MultivariateFreshProbeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/- The literal finite-variable dictionary tree of paper07 Definition2.1.
The coefficient vector is a finite list, extended by zero outside its length.
Validity and canonical storage are separate propositions, not constructors. -/
mutual
  inductive MultivariateCollectedNF where
    | mk : Nat → List Nat → MultivariateCollectedTags → MultivariateCollectedNF
  inductive MultivariateCollectedTags where
    | nil : MultivariateCollectedTags
    | cons : NONote → MultivariateCollectedNF → Nat → MultivariateCollectedTags → MultivariateCollectedTags
end

def multivariateCoefficientCode : List Nat → Nat
  | [] => 0
  | a::rest => Nat.pair a (multivariateCoefficientCode rest)+1

mutual
  def multivariateCollectedCode : MultivariateCollectedNF → Nat
    | .mk c b tags => Nat.pair c (Nat.pair (multivariateCoefficientCode b) (multivariateCollectedTagsCode tags))
  def multivariateCollectedTagsCode : MultivariateCollectedTags → Nat
    | .nil => 0
    | .cons rho A a rest => Nat.pair
        (Nat.pair (rawNoteEncode rho.1) (multivariateCollectedCode A))
        (Nat.pair a (multivariateCollectedTagsCode rest))+1
end

def multivariateCollectedTagKey (rho : NONote) (A : MultivariateCollectedNF) : Nat :=
  Nat.pair (rawNoteEncode rho.1) (multivariateCollectedCode A)

def multivariateCoefficientAdd : List Nat → List Nat → List Nat
  | [], right => right
  | left, [] => left
  | a::left, b::right => (a+b)::multivariateCoefficientAdd left right

def multivariateVariableCoefficients (i a : Nat) : List Nat :=
  if a=0 then [] else List.replicate i 0 ++ [a]

def multivariateCoefficientValue : List Nat → (Nat → Nat) → Nat
  | [], _ => 0
  | a::rest, rho => a*rho 0 + multivariateCoefficientValue rest (fun i => rho (i+1))

mutual
  noncomputable def actualMultivariateCollectedValue : MultivariateCollectedNF → (Nat → Nat) → Nat
    | .mk c b tags, rho => c+multivariateCoefficientValue b rho+
        actualMultivariateCollectedTagsValue tags rho
  noncomputable def actualMultivariateCollectedTagsValue : MultivariateCollectedTags → (Nat → Nat) → Nat
    | .nil, _ => 0
    | .cons head A a rest, rho => a*actualProfileHead head (actualMultivariateCollectedValue A rho)+
        actualMultivariateCollectedTagsValue rest rho
end

def multivariateCollectedTagInsert (rho : NONote) (A : MultivariateCollectedNF) (a : Nat) :
    MultivariateCollectedTags → MultivariateCollectedTags
  | .nil => if a=0 then .nil else .cons rho A a .nil
  | .cons sigma B b rest =>
    if a=0 then .cons sigma B b rest
    else if multivariateCollectedTagKey rho A<multivariateCollectedTagKey sigma B then
      .cons rho A a (.cons sigma B b rest)
    else if multivariateCollectedTagKey rho A=multivariateCollectedTagKey sigma B then
      .cons sigma B (a+b) rest
    else .cons sigma B b (multivariateCollectedTagInsert rho A a rest)

def multivariateCollectedTagsMerge : MultivariateCollectedTags → MultivariateCollectedTags → MultivariateCollectedTags
  | .nil, right => right
  | .cons rho A a rest, right => multivariateCollectedTagInsert rho A a
      (multivariateCollectedTagsMerge rest right)

def multivariateCollectedAdd : MultivariateCollectedNF → MultivariateCollectedNF → MultivariateCollectedNF
  | .mk c b tags, .mk d e rest => .mk (c+d) (multivariateCoefficientAdd b e)
      (multivariateCollectedTagsMerge tags rest)

/- Exact grammar of the computed fresh-head normal form. Original heads
have their original bounded code; variable heads contain the literal input
normal form and a variable in the actual finite source scope. -/
mutual
  def MultivariateProbeNFShape (d cap : Nat) : CollectedPositiveNF → Prop
    | .mk _ b tags => b=0 ∧ MultivariateProbeTagsShape d cap tags
  def MultivariateProbeTagsShape (d cap : Nat) : CollectedPositiveTags → Prop
    | .nil => True
    | .cons rho A _ rest =>
      ((∃ i : Nat, positiveVariableHeadIndex cap rho=some i ∧ i<d ∧ A=.mk 0 1 .nil) ∨
        (rawNoteEncode rho.1≤cap ∧ MultivariateProbeNFShape d cap A)) ∧
      MultivariateProbeTagsShape d cap rest
end

/- Decode actual fresh-head collection into literal coefficients and
original-head tags. Freshness/canonicality are proved separately. -/
mutual
  noncomputable def decodeMultivariateCollected (cap : Nat) : CollectedPositiveNF → MultivariateCollectedNF
    | .mk c _ tags => multivariateCollectedAdd (.mk c [] .nil) (decodeMultivariateCollectedTags cap tags)
  noncomputable def decodeMultivariateCollectedTags (cap : Nat) : CollectedPositiveTags → MultivariateCollectedNF
    | .nil => .mk 0 [] .nil
    | .cons rho A a rest =>
      match positiveVariableHeadIndex cap rho with
      | some i => multivariateCollectedAdd (.mk 0 (multivariateVariableCoefficients i a) .nil)
          (decodeMultivariateCollectedTags cap rest)
      | none => multivariateCollectedAdd (.mk 0 []
          (.cons rho (decodeMultivariateCollected cap A) a .nil))
          (decodeMultivariateCollectedTags cap rest)
end

noncomputable def multivariateCollectedNormalizeAt (cap : Nat) (E : MultivariatePositiveExpr) :
    MultivariateCollectedNF :=
  decodeMultivariateCollected cap (collectedPositiveNormalize (multivariatePositiveProbe cap E))

end LogicLineages.OrdinalComparison
