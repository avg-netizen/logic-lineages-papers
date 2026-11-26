# Checked raw DAG composition: exact next plan

## Boundary

RawSourceDAG accepts precisely actual typed graph/root encodings and proves concrete valid/reify computation. RawSourceDAGOperations supplies exact append/insert/rename reference/table identities and primitive unchecked structural maps. This proposal adds genuine checked composition, not merely success assuming typed inputs. Original source compiler computability and all-gate normalization are still later stages.

## A. Small first packet: application and eraser

Define explicit raw list constructors, then checked wrappers returning Option Code:

* Application, with explicit desired output type code t: require both inputs valid, identical raw free contexts, and function output type = arrowCode(argument output type,t). Append the argument table before the function table in newest-first storage. Add one actual application node with payload [argument-type, argument-table-length + function-root, argument-root], empty local prefix, output t, root 0. Literal length is sum+1.
* Eraser: require both inputs valid, identical free contexts, and both output type codes zero (ground). Insert a ground local binder into the first graph, append the second graph, add a lambda with payload [0,0,second-table-length+first-root], then application with payload [0,0,1+second-root]. Final type ground/root0. Literal length is sum+2.

Checked wrappers use concrete guards and return none exactly when those guards fail, not a postulated compatibility predicate. For every correctly typed pair, output is some exact encode of ScopedDAG.application/eraser. Conversely every successful raw output has actual typed compatible input witnesses and is exactly the encoding of that actual composition; output is accepted by actual decoder. No root/graph equality is weakened to term denotation. Generic contexts and all input source constructors allowed; repeated and unused vertices retained. Functions are jointly Computable from already-proved valid computation plus primitive raw list routines. Full input compatibility includes type checks even if the raw graph independently validates.

Underlying raw constructors can be total unchecked helpers; external rejection applies to the checked wrappers. Their raw sizes are explicit for all inputs, with conditional successful size conclusions for wrappers. Deriving typed witnesses for soundness is legitimate only because the computing wrapper itself is concrete numeric/list code, never a choice-based function.

## B. Following concrete derived operations

Zero, variable and successor constructors with checked type/finite-index arguments; checked renaming table validation with actual typed, possibly noninjective renaming; detectorLeft/Right and right-fold aggregate with common declared context/ground input validation. Empty aggregate is the literal two zero-source graphs, not a scalar-zero assertion. Exact detector count is 2*(na+nb)+6; aggregate per side is sum(2*(na+nb)+8)+1, matching actual weight.

For magnifyInput/identityInput/constantInput/upperInput/lowerInput, use their literal definitions, not a semantically equivalent eraser shortcut. Specifically magnifyInput places lambda then zero then application on inserted input (newest-first application/zero/lambda). This differs in table order from eraser(input,zero), despite equal term semantics. Identity/constant add their own var-or-zero/lambda/application chain, preserving shifted original root. Prove exact encoded table identity and +3/+6 counts. Checked wrappers reject malformed or nonground inputs.

## C. Remaining compiler obligations

Real all-four arithmetic gate codes including sort, all Boolean DAG constructors/shared references, all five Program constructors and complete accepted source-input normalization, literal typed Plan/forest/aggregate/wrapper reconstruction, total malformed handling and joint Computable composition. Existing polynomial actual shared-table bounds become usable only through those exact reconstruction theorems. No bit-runtime theorem is required or claimed.

Request conceptual approval for first small application/eraser checked packet, then exact freeze before proof. Separate primitive raw constructors, typed exactness and arbitrary-success soundness may be bounded proof roots under unchanged caps; a fresh full packet gate remains required.
