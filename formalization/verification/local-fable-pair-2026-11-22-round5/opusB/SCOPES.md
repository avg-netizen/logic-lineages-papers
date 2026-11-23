# Opus B round-5 scopes (three lines each)

## 1. Even tag of a numeral — `LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformTagProof`
- Says: for every positive body and every x, the calculus derives `tagTerm false (numeral x) = numeral (2x)` (`exact_EvenTagNumeral`), by induction from the accepted internal tag arithmetic.
- Assumes: nothing; receipt `1795405399179687850-3294761`; axioms propext/Quot.sound.
- Serves: `thm:upper` (uniform-to-individual bridge, step iii) / `lem:arithmetic-accessibility` interface.

## 2. All-terms instance — `LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformInstanceProof`
- Says: from a derivation of the all-terms sentence of a presentation at context c, the calculus derives `carrier d false c (numeral x) → membership false (numeral x)` for every x (`exact_AllTermsInstance`).
- Assumes: nothing; receipt `1795405423235299499-3294855`; axioms propext/Quot.sound.
- Serves: `thm:upper` (bridge step i).

## 3. Scalar carrier truth at numerals — `LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformCarrierProof`
- Says: if the presentation's scalar checker evaluates to 1 at (c, x), the calculus derives the carrier formula `carrier d false c (numeral x)` (`exact_ScalarCarrierNumeralTruth`), from the accepted numeral evaluation of programs.
- Assumes: nothing; receipt `1795405447609717273-3294906`; axioms propext/Classical.choice/Quot.sound.
- Serves: `thm:upper` (bridge step ii).

## 4. Uniform-to-individual bridge — `LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformBridgeProof`
- Says: for every closed window and checker programs evaluating its original four checks, ID₁-derivability of the all-terms sentence at context c gives an ID₁ derivation of the atom I(numeral (2x)) for every admitted scalar address x (`exact_UniformToIndividual`).
- Assumes: nothing; receipt `1795405499583388240-3295092`; axioms propext/Classical.choice/Quot.sound.
- Serves: `thm:upper` (the internal hypothesis becomes the all-terms form).

## 5. Conditional `thm:upper`, uniform form — `LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformProof`
- Says: for every ordinal BH, E4 (Pohlers' norm bound for derivable atoms) and the uniform internal accessibility (for each closed window, the all-terms sentence is ID₁-derivable at some programs evaluating its original checks and some context) imply that the confined strict relation is well founded and every typed ordinary term has confined rank < BH (`exact_ConditionalUpperUniform`).
- Assumes: E4 `NormTheorem BH`, `UniformAccessibility`; frozen target sha cdb68486…33e8; receipt `1795405517923316778-3295168`; axioms propext/Classical.choice/Quot.sound.
- Serves: `thm:upper` (conditional).

## 6. Conditional Paper 16 `thm:main`, uniform form — `LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformMain16Proof`
- Says: items 1–5 and, under E1–E4 and the uniform internal accessibility, item 6 (`exact_ConditionalMain16Uniform`), as in #1467 with the uniform hypothesis in place of the individual one.
- Assumes: E4, `UniformAccessibility`, E1 `Calibration D`, E2 `TowerHypotheses D`, E3 `BHIdentification D BH`; receipt `1795405528567519678-3295201`; axioms propext/Classical.choice/Quot.sound.
- Serves: Paper 16 `thm:main` (conditional).
