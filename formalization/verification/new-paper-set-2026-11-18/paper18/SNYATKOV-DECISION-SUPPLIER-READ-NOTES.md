# Author's actual supplier trace (for independent final review)

This is a read audit, not the independent final acceptance or a native receipt.

- **Original reduct and compiler.** `ControlDefinitions` recurses at the
  literal seed n at every F successor and uses level 5 at n+100. The
  `BaseTerm` constructors use that `Phi` for arbitrary nested nonlinear
  inputs, and hold the same raw variable numbers. `ContractDefinitions`
  covers all equality, less-than, negation, conjunction and existential
  natural binders with the same `Function.update`; nesting expresses all
  alternations with repeated names. The active `SourceDecisionWorkingDefinitions`
  uses tags 0/1 for two-term atoms, 2 for negation, 3 for conjunction, 4 for
  projection of the recursively eliminated body. No encoded binder is
  rejected and the code does not substitute an unrelated witness or add any
  source-language atom. `SourceCompilerCalibrationProof` inducts on
  `BaseTerm` then `SourceFormula`; `embedding_step` and `compiler_step`
  relate radix arithmetic directly to each constructor, and the binder case
  uses the real initialized-projector calibration, not a Boolean-fragment
  theorem. `SourceCompilerProgramsProof` supplies strictly smaller raw
  children from division/unpairing and gives actual computable assembly
  functions. Binder assembly applies `WholeBoundProjectionCodeProof.actualJointProgram`
  to the computed lists and graph; no normalization oracle is a premise.
- **Why the decreasing graph proves computation.** In
  `FiniteGraph.Proof.exactDecreasingGraph`, computability of children,
  assemble, and measure supplies a computable finite graph with depth
  `μ a + 1`; strict descent and the displayed recurrence identify its
  singleton root with `(a, f a)`. Head lookup and second projection recover
  the recursive value. This proves `Computable f`, not merely termination
  on typed code or calibration at an assumed semantic evaluator.
- **Old/current binder correspondence.**
  `BooleanGraphCodeWorkingDefinitions.startFor` uses term support of the
  whole forest; `BooleanGraphCodeCalibrationProof.literalFreshAllocation`
  proves equality to matrix-variable support using exact forest support.
  It calibrates the allocation and whole graph on every typed Matrix;
  `literalCompiler` retains the total functional graph outside the
  arbitrary Boolean predicate. Independent current 378 calibration uses
  direct matrix support. Both allocate exactly the names of the one
  `ExpandedBooleanGraph` at reserved list [i], and the new proof relates
  their literal wrapper codes without inferring any all-raw equality.
  The actual wrapper keeps the leading i and consumes the only bound-list
  parameter, together with the same graph, in 393's initialized program.
  Its semantic theorem is not applied to H-bearing matrices: existing
  `OriginalSourceEliminationProof.hFreeSourceOutput` derives H-freeness
  inductively and then `actualSourceElimination` uses the original typed
  binder proof (functional graph and whole-block projection at common
  valuation); likewise `originalSourceNameSupport` proves no free-name
  introduction at any recursive step. No H-language QE is inferred.
- **Zero evaluation and conventions.** Active `groundTerm` uses the actual
  all-zero variable value and every original expanded arithmetic operation
  on raw encoded arguments. Subtraction is truncated Nat subtraction;
  `groundTerm` computes right/left for a stored (divisor, term), and
  Nat division by zero stays zero. `groundMatrix` calls decidable Nat
  divisibility and its computability proof uses the equivalent mod test;
  for modulus zero this is equality to 0, not a positive residue predicate.
  Both graph normalizers separately emit a genuine equation for this tag.
  The lower internal stored index 0 denotes modulus 1, not expanded zero.
  `SnyatkovInverseDefinitions.floorInverse` is
  `Nat.findGreatest (fun n => g n ≤ x) x`; exact inverse graphs omit the
  lower inequality at n=0 but retain the upper inequality, giving the
  intended below-range totalization. `actualPrimitiveRecursion.1` uses
  `Primrec.nat_findGreatest` and actual Phi, not a supplied inverse.
  `GroundEvaluatorCalibrationProof` does a typed Term/Matrix induction
  through every tag and uses real Boolean negation/conjunction/disjunction
  semantics. `GroundEvaluatorProgramsProof` gives raw decreasing graphs
  with actual decidable arithmetic and fixed-control/finite-search
  primitive recursion; all raw inputs are total. Auxiliary H evaluation
  computes only an existing numerical function and its inverse.
- **Closing the actual theory.** The new proof does not call the old
  existential full-source theorem. It composes the literal total compiler
  and evaluator, transports syntax code to `OriginalSourceElimination.eliminate`,
  proves every variable occurrence of the result belongs to the original
  (empty) free-name list, then applies actual matrix valuation congruence.
  Typed elimination semantic equivalence pays exact original truth at the
  *arbitrary* valuation. That explicit literal program witnesses the
  frozen independent complete theory endpoint, with no open-formula
  semantics, malformed-raw guarantee, extra admission test, or solver
  hypothesis at the numbered theorem.
