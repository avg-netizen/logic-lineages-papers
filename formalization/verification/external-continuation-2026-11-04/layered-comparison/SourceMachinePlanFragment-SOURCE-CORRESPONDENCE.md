# Actual halting compiler and aggregate syntax fragment

Paper09 hardness.tex lines 281–286 specifies the prime and binder restrictions, and lines 308–314 invokes their preservation by flattening and aggregation. This component instantiates the previously proved literal ground-binder/zero/successor fragment for the actual halting construction, without evaluating or replacing its source terms.

PlanFragment is structural on the unchanged ExistentialPlan.Plan: supplied equation leaves must each satisfy Fragment on their actual DAG.term, done is true, and gates/ground binders recurse. No statement is made about unrestricted supplied DAGs. RenamePreservation uses the actual BinaryPlan.renamePlan, including lifted renamings. ConstructorPreservation covers existing binaryPlan/constantPlan/scalePlan with their exact local-one and fresh-coordinate choices.

CompilerPreservation checks every actual output forest leaf. Generated primitive leaves use the proved Expr fragment result and graph.term realization; original leaves and inherited forest use actual capture-free source/DAG renaming. No Supported, Eval, Holds, valuation, or control hypothesis is required for syntax. In particular, checking the syntax of sort-generated leaves does not transfer sort semantics.

ActualAggregateFragment discharges the invariant for the unchanged SourceMachineConjunctionPlan.plan b e (whose only supplied tail equation is S(port10)=port11), and proves both literal SourceMachineAggregateBridge aggregate outputs satisfy Fragment. The predicate excludes case/recursor and functional-domain binders but does not by itself restrict free-variable types or assert an internal-level bound. All-ground final contexts are a separately accepted result; internal levels at most one remain to be proved separately.

No encoding/effectivity, DAG size transfer, universal theorem promotion, weak comparison or hardness/completeness is asserted. Existing source semantics, manuscripts, register and packages remain unchanged. Candidates absent pending exact review/freeze; no export authorized.
