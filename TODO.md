- Add support for lists, refs, assignment, sequencing, match, fix, loops
- Investigate LoopApp vs FuncApp and if one can be eliminated
- Support for soemthing like uniform(0,1)*uniform(0,1) < theta


CURRENTLY for the generalized discretizer:

1. Find arithmetic predicates whose provenance can't be a scalar cut ("seeds").
2. Group the primitive samples they touch into connected components (union‑find).
3. Compute exact analytic masses (probabilities) of each region the predicates carve out of the joint uniform box, using a small geometry library (1‑D intervals, 2‑D polygon clipping, and circle/disk areas).
4. Replace the whole component with one finite discrete region variable whose values have those probabilities, and rewrite each coupled comparison into a membership test on that variable.