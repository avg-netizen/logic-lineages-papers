# Paper 16: actual original native iterator arithmetic code

The source is the same literal iterator of ordinals.tex:452–467. The new Init-only arithmetic kernel uses the already exact type, variable, lambda, and eraseBound codes, the original ordinary ordered application head, and the original recursor zero/head/three-application spine. It retains the iterator body’s retained function slot 2, erased-index start slot 3 and terminal state slot 0, and adds the original index/function/state binders in their literal order.

The legacy Core equality bridge and independent module-only primitive-recursiveness claim concern the same named kernel. This verifies no semantic iteration, ordinal comparison, cofinality, or extractor/tower effectiveness yet.
