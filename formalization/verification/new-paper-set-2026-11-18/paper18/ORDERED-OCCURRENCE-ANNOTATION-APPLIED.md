# Applied approved binder annotations

SHA256 923b5a1a86030f2654f920b54420d99f01dbbefca18ac0469308d4e23a47978f

```diff
--- 
+++ 
@@ -12,14 +12,14 @@
 def ExactInactive : Prop := ∀ xs p i,
   i ∈ inactive xs p ↔ i ∈ xs ∧ ∀ o ∈ live xs p, (summand o).name ≠ i
 
-def OrderedCoverage : Prop := ∀ xs, xs.Nodup → ∀ ν : Nat → Nat,
+def OrderedCoverage : Prop := ∀ (xs : List Nat), xs.Nodup → ∀ ν : Nat → Nat,
   (∃ i ∈ xs, ∃ j ∈ xs, i ≠ j ∧ ν i=ν j) ∨
     ∃ ys ∈ xs.permutations, (strictOrder ys).eval ν
 
 def MaximumCoverage : Prop := ∀ xs p, live xs p ≠ [] → ∀ ν : Nat → Nat,
   ∃ o ∈ live xs p, (maximal xs p o).eval ν
 
-def TieReduction : Prop := ∀ xs p i j, xs.Nodup → i ∈ xs → j ∈ xs → i ≠ j →
+def TieReduction : Prop := ∀ (xs : List Nat) (p : Formula) i j, xs.Nodup → i ∈ xs → j ∈ xs → i ≠ j →
   (∀ ν, HyperCloseBlock.existsNames xs (.conjunction (.equal (.variable i) (.variable j)) p.compile) ν ↔
     HyperCloseBlock.existsNames (xs.erase i) (p.compile.substitute i (.variable j)) ν) ∧
   (xs.erase i).Nodup ∧ (xs.erase i).length+1=xs.length ∧ (xs.erase i).length<xs.length
```
