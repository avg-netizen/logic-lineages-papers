# Approved qualification applied

Target SHA256: 808c190ffee0524b1808413cbe313082b7473bfb10c7514f310b856091d55abd

```diff
--- 
+++ 
@@ -37,7 +37,7 @@
 
 def ActiveBounds : Prop :=
   (∀ e h k a n,
-    SnyatkovHyperCollision.translatedValue (((n : Int)+e).toNat) h ≤
+    LayeredComparison.SnyatkovHyperCollision.translatedValue (((n : Int)+e).toNat) h ≤
       a*Phi (((n : Int)+k).toNat) → n < ActiveHyper.bound e h k a) ∧
   (∀ i j kind e h k l q a ν,
     (ActiveHyper.guard i j kind e h k l q a).eval ν → ν j < ActiveHyper.bound k l q a)
```
