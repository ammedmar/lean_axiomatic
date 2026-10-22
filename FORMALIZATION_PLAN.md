# Formalizing the axiomatic characterization of cup-i products

Infrastructure assessment and proposed plan, 1 October 2026.

## Recommendation and scope

Use Lean 4 with mathlib, grounded from the outset in its category of chain complexes of `ZMod 2`-modules. Define cup-i coproduct structures there, and use the finite-subset formulation in `sec/reformulation.tex` as coordinates on the actual simplex chain complexes. Prove the combinatorial classification in those coordinates, with explicit compatibility lemmas, and recover the paper's natural constructions on normalized cochains. The finite calculations are meaningful learning exercises within this foundation; the complete theorem is a substantial formalization project with additional categorical work.

The primary target is the current manuscript in this repository, **An axiomatic characterization of Steenrod's cup-i products**. Its statement is stronger than uniqueness up to chain homotopy. The core classification must establish

\[
\exists\,\varepsilon:\mathbb N\to\{0,1\},\quad
\forall i,n,\qquad D_i[n]=T^{\varepsilon(i)}C_i[n],
\]

where (C) is the canonical construction. The same choice of transposition must work in every simplex dimension for a fixed (i). Allowing a separate choice for each pair ((i,n)) would not prove the theorem.

Treat the following as separate deliverables:

1. Definitions of cup-i coproduct structures on mathlib chain complexes over `ZMod 2`, and a formal classification of their simplex coefficient families satisfying the grading, differential identity, non-zero, irreducibility, and freeness conditions.
2. An unconditional existence proof for the canonical family.
3. A bridge identifying those coefficient families with the paper's natural semi-simplicial constructions, and transporting the result to normalized cochains and automorphisms of (W).
4. Optional extensions: independence of the axioms, the stronger result that irreducibility alone implies simpliciality, and comparisons with other formulas and operads.

Deliverable 1 is already valuable. Completion of the paper's main theorem requires 1–3, including simplicial compatibility of the canonical construction.

## What already exists

I inspected current mathlib documentation and source at commit `033c22e2f1d9a1a3d694d8354cb3c4892caee931`. I also checked that the normalized-chain, semi-simplex, and finite-cyclic-resolution source files are present at the stable `v4.34.1` tag. These are source-level findings; I did not compile a Lean project during this investigation.

| Needed component | Existing infrastructure | Work still needed here |
| --- | --- | --- |
| Coefficients and finite combinatorics | `ZMod 2`, `Fin`, `Finset`, powersets, sorting, finite sums | A small API for deleted-vertex sets, ranks, and parity partitions |
| Linear combinations of basis elements | `Finsupp`, linear maps, support submodules | Boundary, transposition, coface maps, and their coefficient formulas |
| Tensor bases | `Module.Basis.tensorProduct`, `TensorProduct.equivFinsuppOfBasisRight` | Identification of the pair-of-subsets model with the tensor-chain model |
| Simplex and semi-simplex categories | `SimplexCategory`, `SemiSimplexCategory`, `SemiSimplexCategory.toSimplexCategory` | Semi-simplicial presheaves and the required chain/representable interface |
| Normalized simplicial chains | `SSet.normalizedChainComplex`, `SSet.normalizedChainComplexMap`, `SSet.normalizedChainComplexFunctorObj` | Explicit identification with the paper's complementary-subset model on representables |
| Generator formulas for normalized chains | `SSet.ιNormalizedChainComplex_d`, `SSet.ιNormalizedChainComplex_eq_zero`, `SSet.normalizedChainComplex_hom_ext` | Characteristic-two simplifications and the formulas used by this proof |
| Tensor products of complexes | `HomologicalComplex.tensorObj`, `ιTensorObj`, `tensorHom`, monoidal structure on nonnegative chain complexes | Concrete coefficient interface and compatibility with transposition |
| Resolution (W) | `Rep.FiniteCyclicGroup.resolution` | Specialization to (C_2) over (mathbb F_2), basis conventions, and the automorphism description |
| Cup-i classification | No ready-made development found in the searches performed | The canonical family, partition-chain argument, freeness lemmas, and uniqueness proof |

The semi-simplex category file explicitly describes semi-simplicial objects as a future interface. Having the category does not mean a complete semi-simplicial homology API is available. Conversely, normalized simplicial chains really are present: the nondegenerate-chain module includes generator maps, their differential, vanishing on degeneracies, and induced maps. The unnormalized `SSet.chainComplex` should not silently be substituted for the paper's normalized complex.

For (C_2) in characteristic two, the cyclic resolution's alternating maps (T-1) and the norm (1+T) coincide. This makes the existing resolution a useful foundation for the final packaging. Exact identification with the paper's (W) remains a proof obligation.

Primary sources:

- [Semi-simplex category](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SimplexCategory/SemiSimplexCategory.html).
- [Normalized chains on nondegenerate simplices](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SimplicialSet/Homology/Nondegenerate.html).
- [Tensor products of chain complexes](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/Monoidal.html).
- [Tensor bases and coefficient equivalences](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/TensorProduct/Basis.html).
- [Finite cyclic projective resolution](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Homological/FiniteCyclic.html).
- [Finite-support linear combinations](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Finsupp/LinearCombination.html).

Lean is my recommendation because the proof uses ordinary finite combinatorics and linear algebra, with existing categorical infrastructure for its eventual interpretation. Cubical Agda has substantial [synthetic cohomology and cup-product formalizations](https://github.com/agda/cubical/blob/master/Cubical/Papers/ComputationalSyntheticCohomology.agda), but that is a different presentation from this paper's concrete normalized-chain operations. I did not conduct an exhaustive comparison of all proof assistants or establish that no cup-i development exists elsewhere.

## A representation that keeps early proofs manageable

### Chain complexes as the foundation

The foundational types should be mathlib's existing complexes:

```lean
-- Proposed aliases; this investigation did not compile them.
abbrev F2 := ZMod 2
abbrev ChF2 := ChainComplex (ModuleCat F2) ℤ
abbrev ChF2Nonneg := ChainComplex (ModuleCat F2) ℕ
```

Both indexing choices exist. Nonnegative indexing matches mathlib's normalized simplicial chains and the resolution (W); integer indexing accommodates the augmented degree (-1) and the paper's grading conventions. Settle the reindexing interface early. In particular, mathlib's `ComplexShape.embeddingDownNat` and `HomologicalComplex.extend` already extend a nonnegative chain complex to an integer-indexed cochain complex by sending degree (n) to (-n), putting zero objects outside the image.

A particularly direct definition of a cup-i coproduct structure is an equivariant **ordinary chain map**

\[
W\otimes C\longrightarrow C\otimes C.
\]

Here (C_2) acts on the first (W)-factor of the source and by transposition on the target. Evaluation on (e_i\otimes c) recovers the degree-(i) linear maps (D_i), and the chain-map equation gives their defining identity. Individual (D_i) are generally not ordinary chain maps. This definition uses tensor complexes and equivariance directly, without first needing to package a closed monoidal structure on the category of complexes.

Relevant additional infrastructure verified in mathlib `v4.34.1`:

- `Mathlib.Algebra.Homology.HomologicalComplex`: complexes, chain maps, componentwise composition, constructors `ChainComplex.of` and `ChainComplex.ofHom`.
- `Mathlib.Algebra.Category.ModuleCat.Abelian`: the abelian category of modules; over a field these objects are vector spaces, without a finite-dimensionality restriction.
- `Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic`, `.Symmetric`, and `.Closed`: tensor products, symmetry, and the tensor–Hom adjunction at the module level.
- `Mathlib.Algebra.Homology.Homotopy`: chain homotopies.
- `Mathlib.Algebra.Homology.BifunctorFlip`: the signed flip for totalized bifunctors, useful with module symmetry to construct tensor transposition. The inspected `Monoidal` file establishes a monoidal structure; do not assume a packaged symmetric structure on complexes merely from the module-level instance.
- `Mathlib.Algebra.Homology.HomotopyCategory.HomComplex`: graded morphisms, their differential, composition, square-zero, identification of degree-zero cocycles with chain maps, and homotopy boundaries. Its supplied bundled `HomComplex` is an integer-indexed **cochain complex of abelian groups**. Its graded pieces have scalar structures and `δ_hom` is linear when the ambient category is linear, so an `F2`-module wrapper can reuse that differential. This is not already a ready-to-use internal Hom object in `ChF2` with every desired adjunction packaged.

Primary references: [complexes](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/HomologicalComplex.html), [module categories](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Category/ModuleCat/Abelian.html), [module-level closed structure](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Category/ModuleCat/Monoidal/Closed.html), [graded Hom complex](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.html), and [bifunctor flip](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/BifunctorFlip.html).

Over `ZMod 2`, signs in tensor differentials, Hom differentials, and graded transposition simplify to (1). These are simplification lemmas to prove using characteristic two, not reasons to redefine the underlying structures. Likewise, preserve actual isomorphisms and chain maps throughout; passing to homotopy or derived categories would forget information needed by the paper's strict uniqueness statement.

### Coordinates on simplex chains

For fixed (n), use finite subsets of `Fin (n + 1)` to represent deleted vertices. Initially use a single ambient vector space of coefficient functions on pairs of subsets:

```lean
-- Proposed types; this sketch has not been typechecked.
abbrev DeletedVertices (n : ℕ) := Finset (Fin (n + 1))
abbrev TensorCoefficients (n : ℕ) :=
  (DeletedVertices n × DeletedVertices n) →₀ ZMod 2
```

Use predicates or submodules to express valid support and degree, rather than placing all degree constraints into dependent types immediately. This reduces transports between equal natural-number expressions. It also allows the augmented and ordinary boundaries to share an ambient coefficient space.

For ordinary chains, valid factors satisfy (|V|\leq n) and (|W|\leq n): the full vertex set represents the augmented degree (-1) generator and must be excluded. For (D_i[n]), express the homogeneous-degree condition without natural-number subtraction:

\[
|V|+|W|+i=n
\qquad\text{whenever the coefficient at }(V,W)\text{ is non-zero}.
\]

Define these conditions separately:

- **Irreducible:** a non-zero coefficient at ((V,W)) implies (V\cap W=\varnothing).
- **Free:** if (i\ne n), a non-zero coefficient at ((V,W)) implies that the coefficient at ((W,V)) is zero. This also forbids fixed points (V=W).
- **Non-zero:** there exist (i,n) with (D_i[n]\ne0). Do not replace this by (D_0[0]\ne0) until the paper's diagonal-propagation argument proves that consequence.
- **Differential identity:** ordinary tensor boundary plus the sum of coface images of (D_i[n-1]) equals ((1+T)D_{i-1}[n]), with explicit zero conventions at (n=0) and (i=0).

Encode the (i=0) identity separately or with an explicit conditional predecessor. Lean's natural-number subtraction makes (0-1=0), whereas the paper means (D_{-1}=0).

For the canonical parity split, define the one-based position of (u\in U) by

\[
1+|\{v\in U:v<u\}|.
\]

Then the parity is that position plus the vertex label. This agrees with the manuscript's (u_j+j), where enumeration starts at one, and avoids using list indexing as the primary definition. Sorting can provide a second description when needed for the existence proof.

Build linear equivalences between this coefficient model and the appropriate tensor-chain spaces alongside the definitions of simplex chains, before treating the coefficient theorem as a theorem about cup-i structures. Writing proofs with coefficients is a representation choice, not permission to omit those equivalences from the full result.

## Milestones and completion criteria

### 0. Learn the proof interface and establish a reproducible project

Create a dedicated `formalization/` Lean project, pin mathlib to `v4.34.1` and Lean to its matching `v4.34.1` toolchain, retrieve its precompiled library cache, and establish a clean build. Establish the `ChF2`/`ChF2Nonneg` aliases and the tensor-complex interface first. Recheck the pin if implementation starts substantially later. Do not use a moving `master` dependency.

The machine has `elan`, `lean`, and `lake`, but its installed toolchains are older than the versions audited here. The default resolves to `v4.34.1`, which was not installed when checked. Setup therefore includes obtaining the matching toolchain; an available launcher alone does not establish a working project.

Work through selected [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) exercises on proofs, sets, functions, finite sums, and algebra. Learn `intro`, `rcases`, `rw`, `simp`, `ext`, `by_cases`, and induction by proving lemmas needed in this project. The first exercises can be transposition involutivity, characteristic-two cancellation, and symmetry of ((1+T)z).

**Done when:** the pinned project builds and contains several small, fully proved lemmas that you can explain from their proof states.

### 1. Prove the freeness lemma as the first substantial result

Build the coefficient/transposition API. First prove the easy corollary: a free chain with ((1+T)z=0) is zero. Then prove the full lemma in `sec/freeness.tex`: if the symmetrization agrees with that of an orbit-representative sum, the free chain chooses exactly one element from each orbit and contains no other terms.

This stage needs neither simplicial sets nor tensor products of complexes. It teaches coefficient extensionality, finite support, and small case splits in (mathbb F_2). It also supplies the lemma used throughout the main proof.

**Done when:** the lemma and both corollaries are proved for arbitrary finite-support chains with an involution and the stated support assumptions.

### 2. Build the simplex model and partition-chain theorem

Construct the ordinary and augmented simplex models as actual mathlib chain complexes with chosen bases. Prove that the coordinate boundaries are the component differentials. Define ordinary and augmented boundaries separately, coface pushforwards as chain maps, and partition chains

\[
\zeta_U=\sum_{V\subseteq U} V\otimes(U\setminus V).
\]

Prove boundary-square-zero, compatibility with transposition, coface chain-map identities, partition-chain symmetry, and the augmented boundary formula. Then prove the largest-irreducible-subcomplex theorem from `sec/irreducible.tex` through coefficients:

1. A reducible coefficient in the boundary detects a pair of partitions differing by transfer of one element.
2. Vanishing reducible boundary makes coefficients invariant under these transfers.
3. An induction transfers all elements from one side to the other, proving constancy across every partition of a fixed union.
4. Such chains are precisely sums of complete partition chains.

This gives the proof's essential lemma without requiring a complete formal Hopf algebra model. The exterior-algebra interpretation can be added later if desired.

Prove the comparison with the ordinary boundary under the degree hypothesis used in the manuscript. The augmented theorem cannot simply be applied to ordinary chains without this comparison.

**Done when:** the partition-chain characterization and its ordinary-chain corollary are unconditional, kernel-checked theorems.

### 3. Define and verify the canonical family

Define (C_i[n]) by summing the two parity parts over subsets of cardinality (n-i), explicitly setting it to zero when (i>n). Prove its grading, non-zero value, irreducibility, freeness, diagonal formulas, and degeneracy vanishing.

The substantial task is the defining differential identity. `sec/existence.tex` imports this from Theorem 10 of **New formulas for cup-i products and fast computation of Steenrod squares** ([paper and source](https://arxiv.org/abs/2105.08025)). Its source contains a sequence of lemmas for face boundaries, coface reindexing, and the final parity cancellation. These need formal proofs; a citation cannot discharge a Lean goal.

Separate the cancellation into coefficients associated with a common deleted-vertex union, and prove the corresponding reindexing or pairing identities. Handle (i=0) directly with the Alexander–Whitney formula if the positive-(i) cancellation requires it. Check the formula against degrees: the downloaded source has an inconsistent index in one displayed statement, while the later proof uses the degree-consistent identity with (D_i\partial).

Stages 3 and 4 can be organized independently in the dependency graph: a provisional classification theorem may explicitly take a verified reference family and its properties as hypotheses. Those hypotheses must be discharged to claim unconditional existence and classification.

**Done when:** the canonical family satisfies every defining condition for all (i,n), with no assumed differential identity, and descends through codegeneracies.

### 4. Formalize the classification proof

Follow the three stages of `sec/proof.tex`:

- For (i>n), prove vanishing from support degree. On (i=n), prove propagation of the diagonal coefficient and use non-zero plus freeness to rule out the everywhere-zero alternative.
- On (i=n-1), obtain the choice function from freeness and use partition chains to force it to be constant within that simplex dimension.
- Define (arepsilon_i) from (D_i[i+1]), and use strong induction on (n-i) to propagate it to all (n). Form the deviation from the twisted canonical family; its reducible boundary vanishes, so it is a sum of partition chains. Its support has at most two partitions of a given union, while a complete family has (2^{n-i}>2) when (n-i>1). Hence the deviation is zero.

Prefer successor-based statements or explicit boundary cases to informal occurrences of (n-2), (n-3), and (i-1). The paper uses negative-index zero conventions at several small-dimensional steps.

**Done when:** the coefficient-family theorem has the quantifiers displayed at the start of this document, including an (n)-independent twist for each (i).

### 5. Recover the paper's theorem

Use representable semi-simplicial sets and their finite-dimensional chain spaces. Prove that arbitrary top-simplex families with the stated identities extend to natural degree-(i) coproducts by evaluating faces, and that restriction recovers the family. Prove both directions of the axiom translations, including freeness on the unique top simplex of a representable.

Identify the subset model with normalized chains on standard simplices, and prove the codegeneracy criterion. For arbitrary simplicial sets, show the canonical construction descends through degeneracies. Then construct cochain products by evaluation of finite chain outputs. Only use finite-dimensional duality on representables: cochains on an infinite simplicial set are not freely spanned by the individual simplex indicator cochains.

Finally identify the degreewise transpositions with automorphisms of (W). Prove both that an arbitrary sequence of choices defines a chain automorphism and that these are all the equivariant chain automorphisms of (W).

**Done when:** the formal statement directly describes the natural constructions in the manuscript, proves existence and uniqueness up to its specified isomorphisms, and proves that the canonical construction is simplicial.

## Computational companion and verification limits

The existing `python/claude_checks/cupi.py` is useful as an executable reference. In a separate, read-only check I verified the canonical identity, grading, irreducibility, and strict freeness in 52 cases covering dimensions 0–7, plus 224 codegeneracy-vanishing cases. These checks support the proposed conventions; they are not proofs in arbitrary dimension and do not validate Lean imports.

There is a specific mismatch to resolve before treating the Python predicates as specifications: `is_free` permits symmetric basis terms. The manuscript's dual freeness condition forbids them when (i\ne n\). For example, the homogeneous chain ({0}\otimes{0}) at ((i,n)=(0,2)) is accepted by the helper but violates that support condition. It is reducible, so this example does not challenge the canonical construction or the main theorem with all hypotheses. Use the strict predicate in the formalization and reconcile the companion separately. The README also references `theorem_check.py`, which is absent from the inspected file inventory.

Use concrete Lean examples as regression checks while proving general theorems. Maintain a theorem ledger linking each manuscript result to its Lean declaration and recording outstanding assumptions. Completion means a reproducible build with no `sorry` or project-specific unproved axioms in the target theorem's dependency graph; inspect theorem assumptions explicitly. Prefer ordinary kernel proofs for finite computations when straightforward.

## Suggested project organization and effort

Other established libraries inspected for the chain-complex foundation:

| Repository | Verified infrastructure | Assessment for this project |
| --- | --- | --- |
| [UniMath, Rocq](https://github.com/UniMath/UniMath/tree/master/UniMath/HomologicalAlgebra) | Integer-indexed complexes in additive categories, their abelian-category structure, cohomology, cones, translations, and homotopy/triangulated constructions | A genuine categorical alternative. A comparable tensor-complex/graded-Hom interface for cup-i structures was not verified in this audit. |
| [MathComp, Rocq](https://github.com/math-comp/math-comp/blob/master/algebra/vector.v) | Finite fields in `algebra/zmodp.v`, finite-dimensional vector spaces, matrices, and linear maps | Strong for finite linear algebra and certified computation. Its inspected core tree does not provide a comparable general chain-complex package; additional homological infrastructure would need separate assessment. |
| [Cubical Agda](https://github.com/agda/cubical/blob/master/Cubical/Algebra/ChainComplex/Base.agda) | Nonnegative chain complexes of abelian groups, chain maps, homotopies, equivalences, and homology | A genuine chain-complex development, alongside synthetic cohomology. The inspected chain foundation is over abelian groups; a comparable tensor/Hom framework over `F2`-modules was not verified. |

These are established repositories, but that does not imply equal coverage of the structures needed here. Mathlib currently offers the most directly matched combination among the libraries inspected. This comparison is based on documentation and source inspection, not builds of the alternative repositories.

Suggested modules, to create after settling definitions:

```text
CupI/Coefficients.lean
CupI/Freeness.lean
CupI/SimplexModel.lean
CupI/PartitionChains.lean
CupI/Canonical.lean
CupI/CanonicalIdentity.lean
CupI/Classification.lean
CupI/Representables.lean
CupI/NormalizedChains.lean
CupI/Resolution.lean
CupI/Main.lean
```

Keep the learning exercises near the mathematics they support. The first checkpoint should be the proved freeness-zero corollary; the next should be a partition-chain result. Reassess scope after those checkpoints, using actual proof effort rather than a calendar promise. For someone learning the assistant, the complete theorem should be budgeted as a project over months. The main uncertainties are the canonical cancellation argument and the representable/normalized-chain bridge, rather than the number of pages in the manuscript.

The most useful immediate next session is to establish the pinned project and prove the freeness-zero corollary together, with you following the proof states. That would test the proposed coefficient representation and provide a small finished theorem before committing to the full categorical development.
