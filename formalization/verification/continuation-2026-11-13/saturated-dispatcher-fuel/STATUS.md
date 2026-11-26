# SaturatedDispatcherFuel: accepted exact1

Frozen preflight `1794601178458769472-7`. Native compile/standard-axiom audit exact1 passed `1794601385862098717-5`:
`SaturatedDispatcherFuel.StatementChecks.internalMonotonicity : Targets.InternalMonotonicity`.

The actual unchanged lineDispatcher AST is used with an explicit saturated axiom leaf. The syntactic certificate excludes fuel input1 while retaining history input2. All other branches and guards are internally fuel-independent; only the actual axiom composition uses saturated leaf internal monotonicity. Both bounds remain internal through additive order, and index/history/encoded line are unchanged. Arbitrary uncalibrated/non-Boolean leaf Programs allowed.

No added assumptions, native reflection, resource-limit changes, or numbered completion claim. This does not establish full kernel/iterator/core fuel preservation. Accepted hashes in ACCEPTED-SHA256SUMS; frozen specifications unchanged. Failed preservation draft retained under failed-drafts. Publication is coordinated separately.
