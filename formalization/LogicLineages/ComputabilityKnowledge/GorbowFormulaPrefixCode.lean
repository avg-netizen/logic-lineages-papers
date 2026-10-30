module

public import LogicLineages.ComputabilityKnowledge.GorbowTermPrefixCode

@[expose] public section

/-! Literal full Gorbow formula prefix syntax. Quantifier bodies have one
additional de Bruijn context position. Distinct U, Ag, K1, K2, T tags are
retained; this is not a proof or semantic truth decision. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowFormulaPrefixCode
open GorbowSyntax

def encode : {n : Nat} → Formula n → List Nat
  | _, .equal t u => 0 :: (GorbowTermPrefixCode.encode t ++ GorbowTermPrefixCode.encode u)
  | _, .universalRelation t => 1 :: GorbowTermPrefixCode.encode t
  | _, .agent t => 2 :: GorbowTermPrefixCode.encode t
  | _, .knowledgeAll t => 3 :: GorbowTermPrefixCode.encode t
  | _, .knowledge t u => 4 :: (GorbowTermPrefixCode.encode t ++ GorbowTermPrefixCode.encode u)
  | _, .truth t => 5 :: GorbowTermPrefixCode.encode t
  | _, .neg φ => 6 :: encode φ
  | _, .imp φ ψ => 7 :: (encode φ ++ encode ψ)
  | _, .conj φ ψ => 8 :: (encode φ ++ encode ψ)
  | _, .disj φ ψ => 9 :: (encode φ ++ encode ψ)
  | _, .all φ => 10 :: encode φ
  | _, .ex φ => 11 :: encode φ

def height : {n : Nat} → Formula n → Nat
  | _, .equal t u | _, .knowledge t u => max (GorbowTermPrefixCode.height t) (GorbowTermPrefixCode.height u) + 1
  | _, .universalRelation t | _, .agent t | _, .knowledgeAll t | _, .truth t => GorbowTermPrefixCode.height t + 1
  | _, .neg φ | _, .all φ | _, .ex φ => height φ + 1
  | _, .imp φ ψ | _, .conj φ ψ | _, .disj φ ψ => max (height φ) (height ψ) + 1

def parse : (n : Nat) → Nat → List Nat → Option (Formula n × List Nat)
  | _, 0, _ => none
  | n, k + 1, 0 :: xs => do
      let (t, ys) ← GorbowTermPrefixCode.parse n k xs
      let (u, zs) ← GorbowTermPrefixCode.parse n k ys
      some (.equal t u, zs)
  | n, k + 1, 1 :: xs => do
      let (t, ys) ← GorbowTermPrefixCode.parse n k xs
      some (.universalRelation t, ys)
  | n, k + 1, 2 :: xs => do
      let (t, ys) ← GorbowTermPrefixCode.parse n k xs
      some (.agent t, ys)
  | n, k + 1, 3 :: xs => do
      let (t, ys) ← GorbowTermPrefixCode.parse n k xs
      some (.knowledgeAll t, ys)
  | n, k + 1, 4 :: xs => do
      let (t, ys) ← GorbowTermPrefixCode.parse n k xs
      let (u, zs) ← GorbowTermPrefixCode.parse n k ys
      some (.knowledge t u, zs)
  | n, k + 1, 5 :: xs => do
      let (t, ys) ← GorbowTermPrefixCode.parse n k xs
      some (.truth t, ys)
  | n, k + 1, 6 :: xs => do
      let (φ, ys) ← parse n k xs
      some (.neg φ, ys)
  | n, k + 1, 7 :: xs => do
      let (φ, ys) ← parse n k xs
      let (ψ, zs) ← parse n k ys
      some (.imp φ ψ, zs)
  | n, k + 1, 8 :: xs => do
      let (φ, ys) ← parse n k xs
      let (ψ, zs) ← parse n k ys
      some (.conj φ ψ, zs)
  | n, k + 1, 9 :: xs => do
      let (φ, ys) ← parse n k xs
      let (ψ, zs) ← parse n k ys
      some (.disj φ ψ, zs)
  | n, k + 1, 10 :: xs => do
      let (φ, ys) ← parse (n + 1) k xs
      some (.all φ, ys)
  | n, k + 1, 11 :: xs => do
      let (φ, ys) ← parse (n + 1) k xs
      some (.ex φ, ys)
  | _, _, _ => none
termination_by _ k _ => k

def decode (n : Nat) (raw : List Nat) : Option (Formula n) := do
  let (φ, rest) ← parse n (raw.length + 1) raw
  if rest = [] then some φ else none
end LogicLineages.ComputabilityKnowledge.GorbowFormulaPrefixCode
