# Exact source correspondence: polynomial collapse graphs

The obligation is paper 08, `thm:graphs`, in `08-multivariate-collapse-comparison/paper.tex`. The frozen endpoint is `PolynomialGraphCompletion.FullPolynomialCollapseGraphs`. It conjoins the complete head-graph package and the complete fixed-expression graph package. Acceptance requires both packages; the head compiler alone does not discharge the source theorem.

## Source heads and literal word language

`PolynomialHeadCoverage` covers every actual ordinal that is a nonzero limit below `omega^omega`, by a normal notation and its literal numeric code. `ValidHead` retains normality, the nonzero-limit condition, and the original strict polynomial bound. No finite degree is fixed across all inputs. `headDegree` and `familyDegree` compute a finite bound from the supplied head codes.

The word alphabet consists of signed constant shifts, `Phi`, quadratic shifts `V_j`, scheduled signed source kernels `X^d_{c,j}`, and scheduled counters `E^d_c`. Kernel and counter degrees range from 3 through the carried degree bound. `letterValue` uses the source scheduled functions. It does not substitute an unrelated total extension on a larger domain. `LetterDomain` states the original nonnegative shifted-input and positive signed-depth conditions and the source budget inequality. The stronger companion startup condition is used only inside the proof that the compiler's generated calls satisfy these original domains.

Words compose unary functions in execution order. Rows are integer constants plus finite integer linear combinations of word values at named raw natural variables. Substitution prepends a unary word to each existing word, preserving a linear combination at the outer level. No compiled letter is applied to a sum of row values.

## Exact doubled graph and exceptional inputs

`compileCalls` starts at `2t` and performs the paper's exit substitution plus twice the counter at each monomial unit. The degree-one contribution is exactly `X = Phi`, `2E = 2`. Degree two uses the signed shift `-((c+1)/2)`, which is minus the natural ceiling of `c/2`, and contributes `Phi(t)-2*((c+1)/2)+2`. Higher degrees retain the literal scheduled `X` and `E` heads.

`headCalls` is calibrated to the accepted principal kernel word, retaining the order and each exact prefix mass. Its exponents are converted to their natural degrees only after proving that every exponent of the normal polynomial head is a positive finite ordinal. The initial shift is exactly the head's source norm.

The accepted principal-word evaluation provides genuine dynamically reached inputs starting at `n+N(head)` for every natural `n`, including zero. Consequently the compiled words satisfy their domains on this entire natural domain. `HeadGraphExact` states `P_head(n)=2*h_head(n)` there. The finite tail cutoff is explicitly zero and the exact finite-exception list is empty. This supplies the source's finite-disjunction graph as one equation, with no omitted natural inputs. The empty exception list is justified by the all-input domain theorem, not by assuming a sufficiently large input.

`HeadGraphTotalFunctional` identifies the graph exactly with the actual collapse function and proves unique existence for every natural input. `HeadEquationExact` turns it into a literal row with symbolic input and output names. `FiniteFamilyDegree` supplies one computed finite bound for each finite collection. `HeadPrograms` proves primitive recursiveness of the actual head-call, word-row, degree, family-bound, and symbolic-row constructors.

## Fixed nesting, arithmetic, and shared names

The expression grammar contains natural constants, original natural variable names, addition, fixed natural multiples, and application of any fixed valid polynomial head. Every syntactic occurrence gets one postorder node name, including repeated occurrences of the same source variable. Its variable equation still refers to that original name. A collapse row uses the child's actual node name as its original argument.

`ExactAllocation`, `FreshSymbolicOutput`, and `GraphSupport` prove the exact contiguous fresh-name allocation, disjointness from original names and the symbolic result, and absence of unbound auxiliary names. `ExpressionDomainsAndDegree` proves that every emitted word has its literal source domain on every natural valuation and stays within the package's common finite degree bound.

`GraphSoundness`, `TotalGraphRealization`, and `AllocatedNodeUniqueness` prove the equations determine exactly the original expression value, that all internal node values exist for every original valuation, and that every allocated node value is unique. The final formula quantifies exactly the allocated names over the naturals. `CorrelatedExistentialGraph` retains the exact equation even if the caller reuses an original name as the result symbol. `TotalFunctionalGraph` supplies unique total output when that result symbol is fresh, as required for ordinary functional graph translation. The separation of these cases prevents a false satisfiability claim for a correlated equation such as `y = y+1`.

## Effective emitted artifact

A fixed radix-five numeric code carries the expression syntax and literal closed head codes. The primitive-recursive parser produces postfix instructions. The row machine allocates one node and emits the corresponding literal row for each instruction. The returned artifact consists of its finite degree bound, complete natural existential prefix, and the rows. `InstructionCodeCalibration`, `RowMachineCalibration`, and `LiteralGraphCompiler` identify this numeric program exactly with the semantic construction. `ActualNumericProgram` proves primitive recursiveness of the parser, machine, and complete package constructor.

This theorem supplies graph translation. It does not assert a decision procedure for the resulting existential word sentences, the pending general guard and row transformations, arbitrary first-order BASE arithmetic, or the internal-level-two comparison consumer.
