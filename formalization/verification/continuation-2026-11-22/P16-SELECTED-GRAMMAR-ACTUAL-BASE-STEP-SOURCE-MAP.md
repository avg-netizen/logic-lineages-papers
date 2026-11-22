# P16 actual selected recursive grammar zero/base and successor split

Draft source only, pending serialized native gate. The selected literal
grammar target and recursive programs are unchanged. No numeric imports
or assumption that two arbitrary calibrated programs have the same
arbitrary-open object graph.

- exact_OpenSelectedGrammarBaseSplit starts from a genuine selected
  grammar state at depth zero and its true left/right pair reads. Original
  literal-zero recursion gives the actual constant pair code. The right
  [0,1] orientation is justified by the original pairing less branch and
  original multiplication/addition laws. Actual object read functionality
  gives empty term code, exact singleton-zero arg code and standard
  scratch cons on the observed args. No sparse cell used for this shape.
- exact_OpenSelectedGrammarSuccessorRow starts with the actual selected
  predecessor and successor states at same H,K,M. Original recursion
  recovery gets the literal step row on the same indices. Composition
  recovery invokes selectedStep on the fixed tape with supplied actual
  ascendingRange(suc M) report and original prior left/right outputs.
- exact_OpenSelectedGrammarSuccessorSplit additionally takes the actual
  successor's left/right reads and invokes the checked selected successor
  splitter to return both genuine component reports besides the selected
  row report. No input- or output-axis inclusion or transport is assumed
  or claimed.

Exact source pins (static closure includes the root):
- NumberedWindowInternalCoverSelectedGrammarTargets.lean: 30b56e9d32535baf568dbd892334f2f8c685d702835e727fafb2ac94dcd39878, static closure (921, 'none')
- NumberedWindowInternalCoverSelectedGrammarOpenTargets.lean: 30b0023d4624f1de05c926068345f13f2d7f078be5cc17b1228f872e4648a02f, static closure (1108, 'none')
- NumberedWindowInternalCoverSelectedGrammarOpenRowProof.lean: 309bbae9f2275a36dccbbf45cb6e392328617651de7ef85d607f6cc795c21a11, static closure (1124, 'none')
- NumberedWindowInternalCoverSelectedGrammarOpenBaseProof.lean: f6d774147007ed97ff779b517f06bf6588529c00aaec89cfbdcad56a0df5648f, static closure (1238, 'none')
- NumberedWindowInternalCoverSelectedGrammarOpenStepProof.lean: 74aa0220207af1131da18142d8f2e480932443b157925786dc2ee8b34c30bc2f, static closure (1371, 'none')
