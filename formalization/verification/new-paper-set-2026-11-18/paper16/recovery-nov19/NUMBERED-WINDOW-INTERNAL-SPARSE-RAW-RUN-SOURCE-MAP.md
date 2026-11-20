# Original numeric raw state iteration and own-witness run

Source-first supporting target only. Keep the accepted literal tick
and its sparse scratch codec unchanged.

| Original source | Exact retained data and comparison |
|---|---|
| `ordinals.tex:31–57,118–125` | Source raw auxiliary reduction has actual nested certificates. Function-side lifting changes the original outer witness code, so preserve the actual source choice of own-code fuel, with no guessed or widened bound. This packet concerns the untyped raw-run core only. |
| `NumberedWindowRawContextAlgorithm.iterate/run/raw/windowStep` | Original iterate applies tick first and recurses with the remaining fuel. Original run starts at (false,some(q,w,r)) and returns its final flag. The wrapper `raw` later uses w for both run fuel and input witness, with separate actual syntax tests; `windowStep` still separately checks both typed admitted endpoints. The latter tests are **not** erased or claimed here. |
| Original #688–690 `...InternalSparseRawTickTargets` / `...NumericChecks` | Same physical chosenTick p other on exact pack [flag,frameOption] scratch, same actual original root/fallback numerical calibrations explicitly required. Fallback executable choice already exists; no arbitrary open semantics, old graph or body equivalence is inferred. |
| `GorbowPRProgramDefinitions.evaluate` | Original arithmetic AST recursion has [fuel,scratch], base projection at scratch, step input [prior fuel,previous result,initial scratch]. The step selects only previous result for chosenTick. The recurrence first advances the original head-first iterate via the original commute identity tick(iterate fuel s)=iterate fuel (tick s); prove it from original recursion rather than assuming computation order equality. |
| `NumberedWindowFieldAlgorithm.pack` / original sparse pair and cell decoding | Construct actual optional frame as 1+pack [q,w,r], and initial scratch as pack [0,that frame]. Decode final first field by the real sparse cellHead; the exact certified loop state has private scratch shape, not arbitrary bytes across this comparison. |

Exact comparisons: initial scratch code, actual Program2 recurrence for
every original encoded state and arbitrary fuel, and actual Program3
own-code run for all raw q/w/r (including malformed). The last really
calls iterate with w and retains w in the initial frame, so zero fuel
and terminal identity have their old meanings. No callback open laws,
terminal invariant proof, arithmetical first-tick/fuel extension,
typed raw5 acceptance, least compatibility, full RawMatching or
internal ID1 accessibility is asserted.
