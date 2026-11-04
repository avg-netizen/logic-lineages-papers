# Exact arithmetic inverse supplier, 3 November2026

Original target: paper08 theorem snyatkov, the actual f=Phi and fixed-seed H
expanded arithmetic language, not a changed growth control or variable-seed
iteration. Primary: A.S.Snyatkov,2008, pp39–51,
https://eprints.tversu.ru/id/eprint/494/1/19950136_2008_2_snyatkov.pdf .
Downloaded original PDF SHA256 13f5ef161fa40d1bd24de131a0cbe450e9a51cf5a4b9514f5ee48bd2deb8019e.
Directly inspected pp40–42 definitions/inverse and Lemma3, and p50 Theorem2.
The PDF text has broken legacy glyph encoding; rendered primary pages supply
those checks. Inverse means greatest n with g(n)≤x, with0 below g(0). The
unconditional graph is (n=0 OR g(n)≤x) AND x<g(n+1); omitting the first disjunct
would falsely discard the prescribed below-range default. The actual primitive
bounded search uses x itself, justified by g(n)>n for the actual controls.

This checkpoint implements the source-expanded-language inverse functions and
an effective version of source Lemma3, with d(a)=a for actual Phi and H. The
actual controls have uniform doubling, so this stronger explicit total bound
covers every natural coefficient and argument, including zero. No missing
Snyatkov theorem, oracle predicate or class field is assumed. Full expanded
language elimination/normal forms and quantified BASE decision remain pending.
Main separately owns BalancedSentence* logical translation; no overlap.

Comparator Definitions/Targets must compile and freeze before proof authorship.
Accepted source from prior checkpoints remains immutable. New exact gates use
only the existing bounded serialized check.py profile; no compiler started at
this source selection stage.
