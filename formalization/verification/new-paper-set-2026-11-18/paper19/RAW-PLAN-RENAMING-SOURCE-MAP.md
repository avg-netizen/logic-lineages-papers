# Raw Plan renaming for continuation-based literal lowering

The paper19 compiler lowers binary constants with the actual
`BinaryPlan.binaryPlan`. Its recursive cases shift the complete continuation
under one or three fresh ground binders. This supporting comparator concerns
the literal `BinaryPlan.renamePlan` transformation on arbitrary typed Plans.

The raw scan preserves every instruction position. It uses the existing
exact unchecked raw source-DAG transformation on each equation and the
exact numeric gate port mapping on all four gates. A ground binder prepends
ground to the declared target context and lifts the table by adding the
new zero index and incrementing the older indices. The result reverses the
scan accumulator once to recover original instruction order.

The typed endpoint is exact at every source and target type context with
every dependent typed renaming. The primitive-recursive computation
endpoint is total over all raw inputs. The function is a structural
operation for callers that already have compatible typed renamings.
