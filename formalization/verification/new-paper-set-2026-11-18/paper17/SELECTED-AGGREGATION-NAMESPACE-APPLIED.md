--- SelectedAggregationDefinitions original
+++ SelectedAggregationDefinitions corrected
@@ -5,6 +5,7 @@
 @[expose] public section
 namespace LogicLineages.PermittedControl.SelectedAggregation
 open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector
+open Source.AdmissibleSum
 
 /-- Actual successful finite output, ruling out fallback-zero reasoning. -/
 def GroundResult {Γ} (ctrl : Nat → Nat) (policy : Policy)
51506e6c6ab40a5c4d970ea75c305628f70a3e00e761c59c87472640bb667b35
--- SelectedAggregationTargets original
+++ SelectedAggregationTargets corrected
@@ -3,6 +3,7 @@
 @[expose] public section
 namespace LogicLineages.PermittedControl.SelectedAggregationTargets
 open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector SelectedAggregation
+open Source.AdmissibleSum
 open OrdinalComparison.ParametricActualCollapse
 
 def SixEraserCollision : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K →
ad32b043ec40a6669d67c0b119e83eafc73b3d5bb10bdb86c422a1f773382d0c
